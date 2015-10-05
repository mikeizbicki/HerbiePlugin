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
import Data.List.Split
import Data.Maybe
import Data.Ratio

import Herbie.CoreManip
import Herbie.MathExpr

import Prelude
import Show

-- import Debug.Trace hiding (traceM)
trace a b = b
traceM a = return ()

--------------------------------------------------------------------------------

-- | The fields of this type correspond to the sections of a function type.
--
-- Must satisfy the invariant that every class in "getCxt" has an associated dictionary in "getDicts".
data ParamType = ParamType
    { getQuantifier :: [Var]
    , getCxt        :: [Type]
    , getDicts      :: [CoreExpr]
    , getParam      :: Type
    }

-- | This type is a simplified version of the CoreExpr type.
-- It only supports math expressions.
-- We first convert a CoreExpr into a MathInfo,
-- perform all the manipulation on the MathExpr within the MathInfo,
-- then use the information in MathInfo to convert the MathExpr back into a CoreExpr.
data MathInfo = MathInfo
    { getMathExpr   :: MathExpr
    , getParamType  :: ParamType
    , getExprs      :: [(String,Expr Var)]
        -- ^ the fst value is the unique name assigned to non-mathematical expressions
        -- the snd value is the expression
    }

-- | Pretty print a math expression
pprMathInfo :: MathInfo -> String
pprMathInfo mathInfo = go 1 False $ getMathExpr mathInfo
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
--                     EMonOp "negate" l@(ELit _) -> "-"++go i False l
                    EMonOp "negate" e1 ->     "-"++go i False e1
                    EMonOp op       e1 -> op++" "++go i True  e1

                    EBinOp op e1 e2 -> if op `elem` fancyOps
                        then op++" "++go i True e1++" "++go i True e2
                        else go i parens1 e1++" "++op++" "++go i parens2 e2
                        where
                            parens1 = case e1 of
--                                 (EBinOp op' _ _) -> op/=op'
                                (EMonOp _ _) -> False
                                _ -> True

                            parens2 = case e2 of
--                                 (EBinOp op' _ _) -> op/=op' || not (op `elem` commutativeOpList)
                                (EMonOp _ _) -> False
                                _ -> True

                    ELit l -> if toRational (floor l) == l
                        then if length (show (floor l :: Integer)) < 10
                            then show (floor l :: Integer)
                            else show (fromRational l :: Double)
                        else show (fromRational l :: Double)

                    ELeaf l -> case lookup l $ getExprs mathInfo of
                        Just (Var _) -> pprVariable l mathInfo
                        Just _       -> pprExpr l mathInfo
--                         Just _       -> "???"

                    EIf cond e1 e2 -> "if "++go i False cond++"\n"
                        ++white++"then "++go (i+1) False e1++"\n"
                        ++white++"else "++go (i+1) False e2
                        where
                            white = replicate (4*i) ' '

-- | If there is no ambiguity, the variable is displayed without the unique.
-- Otherwise, it is returned with the unique
pprVariable :: String -> MathInfo -> String
pprVariable var mathInfo = if length (filter (==pprvar) pprvars)
                            > length (filter (==var) $ map fst $ getExprs mathInfo)
    then var
    else pprvar
    where
        pprvar  = ppr var
        pprvars = map ppr $ map fst $ getExprs mathInfo

        ppr = concat . intersperse "_" . init . splitOn "_"

-- | The names of expressions are long and awkward.
-- This gives us a display-friendly version.
pprExpr :: String -> MathInfo -> String
pprExpr var mathInfo = "?"++show index
    where
        index = case findIndex (==var) notvars of
            Just x -> x

        notvars
            = map fst
            $ filter (\(v,e) -> case e of (Var _) -> False; otherwise -> True)
            $ getExprs mathInfo

-- | If the given expression is a math expression,
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

-- | Converts a CoreExpr into a MathInfo
mkMathInfo :: DynFlags -> [Var] -> Type -> Expr Var -> Maybe MathInfo
mkMathInfo dflags dicts bndType e = case varTypeIfValidExpr e of
        Nothing -> Nothing
        Just t -> if mathExprDepth getMathExpr>1 || lispHasRepeatVars (mathExpr2lisp getMathExpr)
            then Just $ MathInfo
                getMathExpr
                ParamType
                    { getQuantifier = quantifier
                    , getCxt = cxt
                    , getDicts = map Var dicts
                    , getParam = t
                    }
                exprs
            else Nothing

    where
        (getMathExpr,exprs) = go e []

        -- this should never return Nothing if validExpr is not Nothing
        (quantifier,unquantified) = extractQuantifiers bndType
        (cxt,uncxt) = extractContext unquantified

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

-- | Converts a MathInfo back into a CoreExpr
mathInfo2expr :: ModGuts -> MathInfo -> ExceptT ExceptionType CoreM CoreExpr
mathInfo2expr guts herbie = go (getMathExpr herbie)
    where
        pt = getParamType herbie

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
            castToType
                (getDicts pt)
                (getParam pt)
                $ App f a'

        -- if statements
        go (EIf cond a1 a2) = do
            cond' <- go cond >>= castToType (getDicts pt) boolTy
            a1' <- go a1
            a2' <- go a2

            wildUniq <- getUniqueM
            let wildName = mkSystemName wildUniq (mkVarOcc "wild")
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
            let tmpName = mkSystemName tmpUniq (mkVarOcc "a")
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
            return $ case lookup str (getExprs herbie) of
                Just x -> x
                Nothing -> error $ "mathInfo2expr: var " ++ str ++ " not in scope"
                    ++"; in scope vars="++show (nub $ map fst $ getExprs herbie)

