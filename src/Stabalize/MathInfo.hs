{-# LANGUAGE FlexibleInstances,FlexibleContexts #-}
module Stabalize.MathInfo
    where

import Class
import DsBinds
import DsMonad
import ErrUtils
import GhcPlugins
import Unique
import MkId
import PrelNames
import TcRnMonad
import TcSimplify
import Type

import Data.Char
import Data.List
import Data.Maybe
import Data.Ratio

import Stabalize.MathExpr

import Prelude
import Show

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

-- | Given a quantified type of the form:
--
-- > forall a. (Num a, Ord a) => a -> a
--
-- The first element of the returned tuple is the list of quantified variables,
-- and the seecond element is the unquantified type.
extractQuantifiers :: Type -> ([Var],Type)
extractQuantifiers t = case splitForAllTy_maybe t of
    Nothing -> ([],t)
    Just (a,b) -> (a:as,b')
        where
            (as,b') = extractQuantifiers b

-- | Given unquantified types of the form:
--
-- > (Num a, Ord a) => a -> a
--
-- The first element of the returned tuple contains everything to the left of "=>";
-- and the second element contains everything to the right.
extractContext :: Type -> ([Type],Type)
extractContext t = case splitTyConApp_maybe t of
    Nothing -> ([],t)
    Just (tycon,xs) -> if (occNameString $ nameOccName $ tyConName tycon)/="(->)"
                       || not hasCxt
        then ([],t)
        else (head xs:cxt',t')
        where
            (cxt',t') = extractContext $ head $ tail xs

            hasCxt = case classifyPredType $ head xs of
                IrredPred _ -> False
                _           -> True

-- | given a function, get the type of the parameters
--
-- FIXME: this should be deleted
extractParam :: Type -> Maybe Type
extractParam t = case splitTyConApp_maybe t of
    Nothing -> Nothing
    Just (tycon,xs) -> if (occNameString $ nameOccName $ tyConName tycon)/="(->)"
        then Nothing
        else Just (head xs)


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


----------------------------------------

mkMathInfo :: DynFlags -> [Var] -> Type -> Expr Var -> Maybe MathInfo
mkMathInfo dflags dicts bndType e = case validType of
    Nothing -> Nothing
    Just t -> Just $ MathInfo hexpr (pt { getParam = t}) exprs
    where
        (hexpr,exprs) = go e []

        -- this should never return Nothing if validType is not Nothing
        Just pt = mkParamType dicts bndType

        -- We only return a MathInfo if the input is a math expression.
        -- We look at the first function call to determine if it is a math expression or not.
        validType = case e of
            -- first function is binary
            (App (App (App (App (Var v) (Type t)) _) _) _) -> if var2str v `elem` binOpList
                then Just t
                else Nothing

            -- first function is unary
            (App (App (App (Var v) (Type t)) _) _) -> if var2str v `elem` monOpList
                then Just t
                else Nothing

            -- first function is anything else means that we're not a math expression
            _ -> Nothing

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

mathInfo2expr :: ModGuts -> MathInfo -> CoreM (Expr CoreBndr)
mathInfo2expr guts herbie = go (hexpr herbie)
    where
        t = getParam $ numType herbie

        -- binary operators
        go (EBinOp opstr a1 a2) = do
            a1' <- go a1
            a2' <- go a2
            f <- getDecoratedFunction guts opstr t $ getDicts $ numType herbie
            return $ App (App f a1') a2'

        -- unary operators
        go (EMonOp opstr a) = do
            a' <- go a
            f <- getDecoratedFunction guts opstr t $ getDicts $ numType herbie
            return $ App f a'

        -- if statements
        go (EIf cond a1 a2) = do
            cond' <- go cond
            let wildName = mkSystemName (mkUnique 'z' 1337) (mkVarOcc $ "wild")
--                 wildVar = mkLocalVar VanillaId wildName boolTy vanillaIdInfo
                wildVar = mkLocalVar VanillaId wildName (exprType cond') vanillaIdInfo
            a1' <- go a1
            a2' <- go a2
            return $ Case
                cond'
                wildVar
                t
                [ (DataAlt falseDataCon, [], a2')
                , (DataAlt trueDataCon, [], a1')
                ]

        -- leaf is a numeric literal
        go (ELit r) = do
            fromRationalExpr <- getDecoratedFunction guts "fromRational" t $ getDicts $ numType herbie

            integerTyCon <- lookupTyCon integerTyConName
            let integerTy = mkTyConTy integerTyCon

            ratioTyCon <- lookupTyCon ratioTyConName
            let tmpName = mkSystemName (mkUnique 'z' 1337) (mkVarOcc $ "a")
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

----------------------------------------
-- get information from the environment

-- | Converts a string into a Core variable
getVar :: ModGuts -> String -> CoreM Var
getVar guts opstr = do
    let opname = getName guts opstr
    hscenv <- getHscEnv
    dflags <- getDynFlags
    eps <- liftIO $ hscEPS hscenv
    let optype = case lookupNameEnv (eps_PTE eps) opname of
            Just (AnId i) -> varType i
    return $ mkGlobalVar VanillaId opname optype vanillaIdInfo

    where
        getName :: ModGuts -> String -> Name
        getName guts str = case filter isCorrectVar (concat $ occEnvElts (mg_rdr_env guts)) of
            xs -> if length xs>0
                then gre_name $ head $ xs
                else error $ "getNameParent: '"++str++"'"
            where
                isCorrectVar x = (getString $ gre_name x) == str
                              && (case gre_par x of NoParent -> False; _ -> True)

-- | Like "decorateFunction", but first finds the function variable given a string.
getDecoratedFunction :: ModGuts -> String -> Type -> [Var] -> CoreM CoreExpr
getDecoratedFunction guts str t preds = do
    f <- getVar guts str
    decorateFunction guts f t preds

-- | Given a variable that contains a function,
-- the type the function is being applied to,
-- and all in scope predicates,
-- apply the type and any needed dictionaries to the function.
decorateFunction :: ModGuts -> Var -> Type -> [Var] -> CoreM CoreExpr
decorateFunction guts f t preds = do
    dict <- getDict f
    return $ App (App (Var f) (Type t)) dict
    where
        getDict :: Var -> CoreM CoreExpr
        getDict op = do
            let ([v],unquantified) = extractQuantifiers $ varType op
                ([pred],_) = extractContext unquantified
                pred' = substTyWith [v] [t] $ pred

            ret <- getDictionary guts pred'
            case ret of
                Just x -> return x
                Nothing -> case getPredEvidence pred' (map Var preds) of
                    Just x -> return x
                    Nothing -> error $ "getDict: could not find dictionary for "++getString op

-- | Given a predicate for which we don't have evidence
-- and a list of expressions that contain evidence for predicates,
-- construct an expression that contains evidence for the given predicate.
getPredEvidence :: PredType -> [CoreExpr] -> Maybe CoreExpr
getPredEvidence pred xs =
--     trace ("getDictExprFor: c="++getString c
--          ++"; varTy="++showSDoc dynFlags (ppr varTy)
--          ++"; xs="++showSDoc dynFlags (ppr xs)
--           ) $
    go xs
    where
        -- We expect pred to have exactly one type variable within it,
        -- which we extract here.
        varTy :: Type
        varTy = case getTyVar_maybe pred of
            Just x -> mkTyVarTy x
            Nothing -> error $ "getPredEvidence: unsupported predicate "++showSDoc dynFlags (ppr pred)
--         varTy = case classifyPredType pred of
--             ClassPred _ [varTy] -> varTy

        -- Recursively descend into all the available predicates.
        -- The list of expressions will grown as we recurse.
        go :: [CoreExpr] -> Maybe (CoreExpr)
        go []           = Nothing
        go (expr:exprs) = if exprType expr == pred

            -- The expression we've found matches the predicate.
            -- We're done!
            then Just expr

            -- The expression doesn't match the predicate,
            -- so we recurse by searching for sub-predicates within expr
            -- and adding them to the list.
            else case classifyPredType (exprType expr) of

                -- What we've found contains no more predicates to recurse into,
                -- so we don't add anything to the list of exprs to search.
                IrredPred _ -> go exprs
                EqPred _ _ _ -> go exprs

                -- We've found a class dictionary.
                -- Recurse into each field (selId) of the dictionary.
                -- Some (but not all) of these may be more dictionaries.
                ClassPred c' [ct] -> go $ exprs++
                    [ App (App (Var selId) (Type varTy)) expr | selId <- classAllSelIds c' ]

                -- We've found a tuple of evidence.
                -- For each field of the tuple we extract it with a case statement, then recurse.
                TuplePred preds -> go $
                    [ Case expr wildVar (varType $ tupelems!!i)
                        [ ( DataAlt $ tupleCon ConstraintTuple $ length preds
                          , tupelems
                          , Var $ tupelems!!i
                          )
                        ]
                    | (i,t) <- zip [0..] preds
                    ]
                    ++exprs
                    where
                        tupelems =
                            [ mkLocalVar
                                VanillaId
                                (mkSystemName (mkUnique 'z' j) (mkVarOcc $ "a"++show j))
                                (mkAppTy (fst $ splitAppTys t') varTy)
                                vanillaIdInfo
                            | (j,t') <- zip [0..] preds
                            ]

                        -- FIXME:
                        -- If multiple tuples get created in the recursion,
                        -- then there will be multiple variables with the same name and unique.
                        -- These variables never actually get referenced,
                        -- so I don't think this is a problem.
                        -- But it is a code smell.
                        wildName = mkSystemName (mkUnique 'z' 1337) (mkVarOcc $ "wild")
                        wildVar = mkLocalVar VanillaId wildName (exprType expr) vanillaIdInfo

-- | Given a non-polymorphic PredType (e.g. `Num Float`),
-- return the corresponding dictionary.
getDictionary :: ModGuts -> Type -> CoreM (Maybe CoreExpr)
getDictionary guts dictTy = do
    let dictVar = mkGlobalVar
            VanillaId
            (mkSystemName (mkUnique 'z' 1337) (mkVarOcc $ "magicDictionaryName"))
            dictTy
            vanillaIdInfo

    bnds <- runTcM guts $ do
        loc <- getCtLoc $ GivenOrigin UnkSkol
        let nonC = mkNonCanonical $ CtWanted
                { ctev_pred = varType dictVar
                , ctev_evar = dictVar
                , ctev_loc = loc
                }
            wCs = mkSimpleWC [nonC]
        (x, evBinds) <- solveWantedsTcM wCs
        bnds <- initDsTc $ dsEvBinds evBinds

--         liftIO $ do
--             putStrLn $ "dictType="++showSDoc dflags (ppr dictType)
--             putStrLn $ "dictVar="++showSDoc dflags (ppr dictVar)
--
--             putStrLn $ "nonC="++showSDoc dflags (ppr nonC)
--             putStrLn $ "wCs="++showSDoc dflags (ppr wCs)
--             putStrLn $ "bnds="++showSDoc dflags (ppr bnds)
--             putStrLn $ "x="++showSDoc dflags (ppr x)

        return bnds

    case bnds of
        [NonRec _ dict] -> return $ Just dict
        otherwise -> return Nothing

--------------------------------------------------------------------------------
--

runTcM :: ModGuts -> TcM a -> CoreM a
runTcM guts tcm = do
    env <- getHscEnv
    dflags <- getDynFlags
    (msgs, mr) <- liftIO $ initTc env HsSrcFile False (mg_module guts) tcm
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                $ text "Errors:" : pprErrMsgBag errs
                ++ text "Warnings:" : pprErrMsgBag warns
    maybe (fail $ showMsgs msgs) return mr
    where
        pprErrMsgBag = pprErrMsgBagWithLoc

--------------------------------------------------------------------------------
-- utils

getString :: NamedThing a => a -> String
getString = occNameString . getOccName

expr2str :: DynFlags -> Expr Var -> String
expr2str dflags (Var v) = {-"var_" ++-} var2str v
expr2str dflags e       = "expr_" ++ (decorate $ showSDoc dflags (ppr e))
    where
        decorate :: String -> String
        decorate = map go
            where
                go x = if not (isAlphaNum x)
                    then '_'
                    else x

lit2rational :: Literal -> Rational
lit2rational l = case l of
    MachInt i -> toRational i
    MachInt64 i -> toRational i
    MachWord i -> toRational i
    MachWord64 i -> toRational i
    MachFloat r -> r
    MachDouble r -> r
    LitInteger i _ -> toRational i

var2str :: Var -> String
var2str = occNameString . occName . varName

maybeHead :: [a] -> Maybe a
maybeHead (a:_) = Just a
maybeHead _     = Nothing

myshow :: DynFlags -> Expr Var -> String
myshow dflags = go 1
    where
        go i (Var v) = "Var "++showSDoc dflags (ppr v)
                     ++"::"++showSDoc dflags (ppr $ varType v)
                     ++"; "++showSDoc dflags (ppr $ idOccInfo v)
        go i (Lit (MachFloat  l  )) = "FloatLiteral "  ++show (fromRational l :: Double)
        go i (Lit (MachDouble l  )) = "DoubleLiteral " ++show (fromRational l :: Double)
        go i (Lit (MachInt    l  )) = "IntLiteral "    ++show (fromIntegral l :: Double)
        go i (Lit (MachInt64  l  )) = "Int64Literal "  ++show (fromIntegral l :: Double)
        go i (Lit (MachWord   l  )) = "WordLiteral "   ++show (fromIntegral l :: Double)
        go i (Lit (MachWord64 l  )) = "Word64Literal " ++show (fromIntegral l :: Double)
        go i (Lit (LitInteger l t)) = "IntegerLiteral "++show (fromIntegral l :: Double)++
                                                   "::"++showSDoc dflags (ppr t)
        go i (Lit l) = "Lit"
        go i (Type t) = "Type "++showSDoc dflags (ppr t)
        go i (Tick a b) = "Tick (" ++ show a ++ ") ("++go (i+1) b++")"
        go i (Coercion l) = "Coercion "++myCoercionShow dflags l
        go i (Cast a b)
            = "Cast \n"
            ++white++"(" ++ go (i+1) a ++ ")\n"
            ++white++"("++myshow dflags (Coercion b)++")\n"
            ++drop 4 white
            where
                white=replicate (4*i) ' '
        go i (Let (NonRec a e) b)
            = "Let "++getString a++"::"++showSDoc dflags (ppr $ varType a)++"\n"
            ++white++"("++go (i+1) b++")\n"
            ++drop 4 white
            where
                white=replicate (4*i) ' '
        go i (Let _ _) = error "myshow: recursive let"
        go i (Lam a b)
            = "Lam "++getString a++"::"++showSDoc dflags (ppr $ varType a)++"\n"
            ++white++"("++go (i+1) b++")\n"
            ++drop 4 white
            where
                white=replicate (4*i) ' '
        go i (App a b)
            = "App\n"
            ++white++"(" ++ go (i+1) a ++ ")\n"
            ++white++"("++go (i+1) b++")\n"
            ++drop 4 white
            where
                white=replicate (4*i) ' '
        go i (Case a b c d)
            = "Case\n"
            ++white++"("++go (i+1) a++")\n"
            ++white++"("++getString b++"::"++showSDoc dflags (ppr $ varType b)++")\n"
            ++white++"("++showSDoc dflags (ppr c)++")\n"
            ++white++"["++concatMap altShow d++"]\n"
            ++drop 4 white
            where
                white=replicate (4*i) ' '

                altShow :: Alt Var -> String
                altShow (con,xs,expr) = "("++con'++", "++xs'++", "++go (i+1) expr++")\n"++white
                    where
                        con' = case con of
                            DataAlt x -> showSDoc dflags (ppr x)
                            LitAlt x  -> showSDoc dflags (ppr x)
                            DEFAULT   -> "DEFAULT"

                        xs' = showSDoc dflags (ppr xs)

myCoercionShow :: DynFlags -> Coercion -> String
myCoercionShow dflags c = go c
    where
        go (Refl _ _            ) = "Refl"
        go (TyConAppCo a b c    ) = "TyConAppCo "++showSDoc dflags (ppr a)++" "
                                                 ++showSDoc dflags (ppr b)++" "
                                                 ++showSDoc dflags (ppr c)
        go (AppCo _ _           ) = "AppCo"
        go (ForAllCo _ _        ) = "ForAllCo"
        go (CoVarCo v           ) = "CoVarCo ("++myshow dflags (Var v)++")"
        go (AxiomInstCo _ _ _   ) = "AxiomInstCo"
        go (UnivCo _ _ _ _      ) = "UnivCo"
        go (SymCo c'            ) = "SymCo ("++myCoercionShow dflags c'++")"
        go (TransCo _ _         ) = "TransCo"
        go (AxiomRuleCo _ _ _   ) = "AxiomRuleCo"
        go (NthCo _ _           ) = "NthCo"
        go (LRCo _ _            ) = "LRCo"
        go (InstCo _ _          ) = "InstCo"
        go (SubCo c'            ) = "SubCo ("++myCoercionShow dflags c'++")"


-- instance Show (Coercion) where
--     show _ = "Coercion"
--
-- instance Show b => Show (Bind b) where
--     show _ = "Bind"
--
-- instance Show (Tickish Id) where
--     show _ = "(Tickish Id)"
--
-- instance Show Type where
--     show _ = "Type"
--
-- instance Show AltCon where
--     show _ = "AltCon"
--
-- instance Show Var where
--     show v = getString v


