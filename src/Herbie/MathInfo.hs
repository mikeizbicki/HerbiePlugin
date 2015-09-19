{-# LANGUAGE FlexibleInstances,FlexibleContexts,MultiWayIf,CPP #-}
module Herbie.MathInfo
    where

import Class
import DsBinds
import DsMonad
import ErrUtils
import GhcPlugins hiding (trace)
import Unique
import MkId
import PrelNames
import UniqSupply
import TcRnMonad
import TcSimplify
import Type

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans
import Data.Char
import Data.List
import Data.Maybe
import Data.Ratio

import Herbie.CoreManip
import Herbie.MathExpr

import Prelude
import Show

import Debug.Trace hiding (traceM)
-- trace a b = b
traceM a = return ()

--------------------------------------------------------------------------------

-- | The fields of this type correspond to the sections of a function type.
--
-- Must satisfy the invariant that every class in "getCxt" has an associated dictionary in "getDicts".
data ParamType = ParamType
    { getQuantifier :: [Var]
    , getCxt        :: [Type]
    , getDicts      :: [Var]
    , getParam      :: Type
    }

-- | Convert the type of a function into its ParamType representation
mkParamType :: [Var] -> Type -> Maybe ParamType
mkParamType dicts t = do
    let (quantifier,unquantified) = extractQuantifiers t
        (cxt,uncxt) = extractContext unquantified
    t' <- extractParam uncxt
    Just $ ParamType
        { getQuantifier = quantifier
        , getCxt        = cxt
        , getDicts      = dicts
        , getParam      = t'
        }
    where

-- | Given a type of the form
--
-- > A -> ... -> C
--
-- returns C
getReturnType :: Type -> Type
getReturnType t = case splitForAllTys t of
    (_,t') -> go t'
    where
        go t = case splitTyConApp_maybe t of
            Just (tycon,[_,t']) -> if getString tycon=="(->)"
                then go t'
                else t
            _ -> t


-- dictFromParamType :: Class -> ParamType -> CoreM (Maybe (Expr Var))
-- dictFromParamType c pt =
--     trace ("getDicts="++showSDoc dynFlags (ppr $ getDicts pt)) $
--     return $ getDictExprFor c (getParam pt) (map Var $ getDicts pt)

getClasses :: ParamType -> [Class]
getClasses pt = concat $ map go $ getCxt pt
    where
        go t = case classifyPredType t of
            ClassPred c _ -> [c]
            TuplePred xs  -> concatMap go xs
            _ -> []

getSuperClasses :: Class -> [Class]
getSuperClasses c = c : (nub $ concat $ map getSuperClasses $ concat $ map go $ classSCTheta c)
    where
        go t = case classifyPredType t of
            ClassPred c _ -> [c]
            TuplePred xs  -> concatMap go xs
            _ -> []

--------------------------------------------------------------------------------
-- convert Expr into MathExpr

data MathInfo = MathInfo
    { hexpr :: MathExpr
    , numType :: ParamType
    , getExprs :: [(String,Expr Var)]
    }

herbie2lisp :: DynFlags -> MathInfo -> String
herbie2lisp dflags herbie = mathExpr2lisp (hexpr herbie)

findExpr :: MathInfo -> String -> Maybe (Expr Var)
findExpr herbie str = lookup str (getExprs herbie)

-- | Pretty print a math expression
pprMathInfo :: MathInfo -> String
pprMathInfo mathInfo = go 1 False $ hexpr mathInfo
    where
        isLitOrLeaf :: MathExpr -> Bool
        isLitOrLeaf (ELit _ ) = True
        isLitOrLeaf (ELeaf _) = True
        isLitOrLeaf _         = False

        go :: Int -> Bool -> MathExpr -> String
        go i b e = if b && not (isLitOrLeaf e)
            then "("++str++")"
            else str
            where
                str = case e of
                    EMonOp op e1 -> op++" "++(go i True e1)

                    EBinOp op e1 e2 -> go i parens1 e1++" "++op++" "++go i parens2 e2
                        where
                            parens1 = case e1 of
                                (EBinOp op' _ _) -> op/=op'
                                _ -> True

                            parens2 = case e2 of
                                (EBinOp op' _ _) -> op/=op'
                                _ -> True

                    ELit l -> if toRational (floor l) == l
                        then if length (show (floor l :: Integer)) < 10
                            then show (floor l :: Integer)
                            else show (fromRational l :: Double)
                        else show (fromRational l :: Double)

                    ELeaf l -> case lookup l $ getExprs mathInfo of
                        Just (Var _) -> l
                        _            -> "???"

                    EIf cond e1 e2 -> "if "++go i False cond++"\n"
                        ++white++"then "++go (i+1) False e1++"\n"
                        ++white++"else "++go (i+1) False e2
                        where
                            white = replicate (4*i) ' '


----------------------------------------

-- If the given expression is a math expression,
-- returns the type of the variable that the math expression operates on.
varTypeIfValidExpr :: CoreExpr -> Maybe Type
varTypeIfValidExpr e = case e of

    -- might be a binary math operation
    (App (App (App (App (Var v) (Type t)) _) _) _) -> if var2str v `elem` binOpList
        then if isValidType t
            then Just t
            else Nothing
        else Nothing

    -- might be a unary math operation
    (App (App (App (Var v) (Type t)) _) _) -> if var2str v `elem` monOpList
        then if isValidType t
            then Just t
            else Nothing
        else Nothing

    -- first function is anything else means that we're not a math expression
    _ -> Nothing

    where
        isValidType :: Type -> Bool
        isValidType t = isTyVarTy t || case splitTyConApp_maybe t of
            Nothing -> True
            Just (tyCon,_) -> tyCon == floatTyCon || tyCon == doubleTyCon

mkMathInfo :: DynFlags -> [Var] -> Type -> Expr Var -> Maybe MathInfo
mkMathInfo dflags dicts bndType e = case varTypeIfValidExpr e of
        Nothing -> Nothing
        Just t -> if mathExprDepth hexpr>1 && lispHasRepeatVars (mathExpr2lisp hexpr)
            then Just $ MathInfo
                hexpr
                ( ParamType
                    { getQuantifier = quantifier
                    , getCxt = cxt
                    , getDicts = dicts
                    , getParam = t
                    }
                ) exprs
            else Nothing

    where
        (hexpr,exprs) = go e []

        -- this should never return Nothing if validExpr is not Nothing
        (quantifier,unquantified) = extractQuantifiers bndType
        (cxt,uncxt) = extractContext unquantified

        pt = case mkParamType dicts bndType of
            Just pt -> pt
            Nothing -> error $ "mkMathInfo: varType="++dbg (varTypeIfValidExpr e)++"; bndType="++dbg bndType

        -- recursively converts the `Expr Var` into a MathExpr and a dictionary
        go :: Expr Var
           -> [(String,Expr Var)]
           -> (MathExpr
              ,[(String,Expr Var)]
              )

        -- we need to special case the $ operator for when MathExpr is run before any rewrite rules
        go e@(App (App (App (App (Var v) (Type _)) (Type _)) a1) a2) exprs
            = if var2str v == "$"
                then go (App a1 a2) exprs
                else (ELeaf $ expr2str dflags e,[(expr2str dflags e,e)])

        -- polymorphic literals created via fromInteger
        go e@(App (App (App (Var v) (Type _)) dict) (Lit l)) exprs
            = (ELit $ lit2rational l, exprs)

        -- polymorphic literals created via fromRational
        go e@(App (App (App (Var v) (Type _)) dict)
             (App (App (App (Var _) (Type _)) (Lit l1)) (Lit l2))) exprs
            = (ELit $ lit2rational l1 / lit2rational l2, exprs)

        -- non-polymorphic literals
        go e@(App (Var _) (Lit l)) exprs
            = (ELit $ lit2rational l, exprs)

        -- binary operators
        go e@(App (App (App (App (Var v) (Type _)) dict) a1) a2) exprs
            = if var2str v `elem` binOpList
                then let (a1',exprs1) = go a1 []
                         (a2',exprs2) = go a2 []
                     in ( EBinOp (var2str v) a1' a2'
                        , exprs++exprs1++exprs2
                        )
                else (ELeaf $ expr2str dflags e,[(expr2str dflags e,e)])

        -- unary operators
        go e@(App (App (App (Var v) (Type _)) dict) a) exprs
            = if var2str v `elem` monOpList
                then let (a',exprs') = go a []
                     in ( EMonOp (var2str v) a'
                        , exprs++exprs'
                        )
                else (ELeaf $ expr2str dflags e,(expr2str dflags e,e):exprs)

        -- everything else
        go e exprs = (ELeaf $ expr2str dflags e,[(expr2str dflags e,e)])

mathInfo2expr :: ModGuts -> MathInfo -> ExceptT String CoreM CoreExpr
mathInfo2expr guts herbie = go (hexpr herbie)
    where
        pt = numType herbie

        -- binary operators
        go (EBinOp opstr a1 a2) = do
            a1' <- go a1
            a2' <- go a2
            f <- getDecoratedFunction guts opstr (getParam pt) (getDicts pt)
            return $ App (App f a1') a2'

        -- unary operators
        go (EMonOp opstr a) = do
            a' <- go a
            f <- getDecoratedFunction guts opstr (getParam pt) (getDicts pt)
            return $ App f a'

        -- if statements
        go (EIf cond a1 a2) = do
            cond' <- go cond >>= castToType (map Var $ getDicts pt) boolTy
            a1' <- go a1
            a2' <- go a2

            wildUniq <- getUniqueM
            let wildName = mkSystemName wildUniq (mkVarOcc $ "wild")
                wildVar = mkLocalVar VanillaId wildName boolTy vanillaIdInfo

            return $ Case
                cond'
                wildVar
                (getParam pt)
                [ (DataAlt falseDataCon, [], a2')
                , (DataAlt trueDataCon, [], a1')
                ]

        -- leaf is a numeric literal
        go (ELit r) = do
            fromRationalExpr <- getDecoratedFunction guts "fromRational" (getParam pt) (getDicts pt)

            integerTyCon <- lookupTyCon integerTyConName
            let integerTy = mkTyConTy integerTyCon

            ratioTyCon <- lookupTyCon ratioTyConName
            tmpUniq <- getUniqueM
            let tmpName = mkSystemName tmpUniq (mkVarOcc $ "a")
                tmpVar = mkTyVar tmpName liftedTypeKind
                tmpVarT = mkTyVarTy tmpVar
                ratioConTy = mkForAllTy tmpVar $ mkFunTys [tmpVarT,tmpVarT] $ mkAppTy (mkTyConTy ratioTyCon) tmpVarT
                ratioConVar = mkGlobalVar VanillaId ratioDataConName ratioConTy vanillaIdInfo

            return $ App
                fromRationalExpr
                (App
                    (App
                        (App
                            (Var ratioConVar )
                            (Type integerTy)
                        )
                        (Lit $ LitInteger (numerator r) integerTy)
                    )
                    (Lit $ LitInteger (denominator r) integerTy)
                )

        -- leaf is any other expression
        go (ELeaf str) = do
            dflags <- getDynFlags
            return $ case findExpr herbie str of
                Just x -> x
                Nothing -> error $ "mathInfo2expr: var " ++ str ++ " not in scope"
                    ++"; in scope vars="++show (nub $ map fst $ getExprs herbie)

