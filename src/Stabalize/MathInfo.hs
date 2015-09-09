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
        extractQuantifiers :: Type -> ([Var],Type)
        extractQuantifiers t = case splitForAllTy_maybe t of
            Nothing -> ([],t)
            Just (a,b) -> (a:as,b')
                where
                    (as,b') = extractQuantifiers b

        -- | given unquantified types of the form:
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
        -- FIXME: should we provide a check to ensure that all parameters match?
        extractParam :: Type -> Maybe Type
        extractParam t = case splitTyConApp_maybe t of
            Nothing -> Nothing
            Just (tycon,xs) -> if (occNameString $ nameOccName $ tyConName tycon)/="(->)"
                then Nothing
                else Just (head xs)

-- |
--
-- FIXME: We could cache the classes we've already visited for potentially large speedup.
-- Would this prevent infinite loops?
getDictExprFor :: Class -> Type -> [Expr Var] -> Maybe (Expr Var)
getDictExprFor c t xs = go xs
    where
        go []     = Nothing
        go (x:xs) = case x of
            Var v                   -> processPred $ varType v
            (App (App (Var v) _) _) -> processPred $ getReturnType $ varType v

            a -> error $ "getDictExprFor: "++show a

            where
                processPred t = trace ("processPred; t="++showSDoc dynFlags (ppr t)) $
                  case classifyPredType t of
                    ClassPred c' _ -> if c==c'
                        then Just x
                        else go $ xs++map mkSuperClassDict (classAllSelIds c')
                    TuplePred xs -> listToMaybe $ concatMap (maybeToList . processPred) xs
                    IrredPred x -> go xs
                    EqPred _ _ _ -> error "getDictExprFor: EqPred"

                mkSuperClassDict selId = App (App (Var selId) (Type t)) x

-- | Given a type of the form
--
-- > A -> ... -> C
--
-- returns the type of C
getReturnType :: Type -> Type
getReturnType t = case splitForAllTys t of
    (_,t') -> go t'
    where
        go t = case splitTyConApp_maybe t of
            Just (tycon,[_,t']) -> if getString tycon=="(->)"
                then go t'
                else t
            _ -> t


dictFromParamType :: Class -> ParamType -> CoreM (Maybe (Expr Var))
dictFromParamType c pt = return $ getDictExprFor c (getParam pt) (map Var $ getDicts pt)

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

mathInfo2expr :: ModGuts -> MathInfo -> CoreM (Expr CoreBndr)
mathInfo2expr guts herbie = go (hexpr herbie)
    where
        t = getParam $ numType herbie

        getDict opstr = do
            ret <- getDictConcrete guts opstr (getParam $ numType herbie)
            case ret of
                Just x -> return x
                Nothing -> do
                    ret' <- getDictPolymorphic guts opstr (numType herbie)
                    case ret' of
                        Just x -> return x
                        Nothing -> error $ "getDict: could not find dictionary for "++opstr

        -- binary operators
        go (EBinOp opstr a1 a2) = do
            a1' <- go a1
            a2' <- go a2
            op <- getVar guts opstr
            dict <- getDict opstr
            return $ App (App (App (App (Var op) (Type t)) dict) a1') a2'

        -- unary operators
        go (EMonOp opstr a) = do
            a' <- go a
            op <- getVar guts opstr
            dict <- getDict opstr
            return $ App (App (App (Var op) (Type t)) dict) a'

        -- if statements
        go (EIf cond a1 a2) = do
            cond' <- go cond
            a1' <- go a1
            a2' <- go a2
            return $ Case
--                 (Var $ trueDataConId)
                cond'
                (trueDataConId) -- FIXME: what should this be?
                t
                [ (DataAlt falseDataCon, [], a2')
                , (DataAlt trueDataCon, [], a1')
                ]

        -- leaf is a numeric literal
        go (ELit r) = do
            fromRationalVar <- getVar guts "fromRational"
            fromRationalDict <- getDict "fromRational"

            integerTyCon <- lookupTyCon integerTyConName
            let integerTy = mkTyConTy integerTyCon

            -- FIXME: both of these techniques cause core lint to panic
            ratioTyCon <- lookupTyCon ratioTyConName
--             let ratioTy = mkAppTy (mkTyConTy ratioTyCon) integerTy
--                 ratioConTy = mkFunTys [integerTy,integerTy] ratioTy
            let tmpName = mkSystemName (mkUnique 'z' 1337) (mkVarOcc $ "a")
                tmpVar = mkGlobalVar VanillaId tmpName liftedTypeKind vanillaIdInfo
                tmpVarT = mkTyVarTy tmpVar
                ratioConTy = mkForAllTy tmpVar $ mkFunTys [tmpVarT,tmpVarT] $ mkAppTy (mkTyConTy ratioTyCon) tmpVarT
                ratioConVar = mkGlobalVar VanillaId ratioDataConName ratioConTy vanillaIdInfo

            return $ App
                (App
                    (App
                        (Var fromRationalVar )
                        (Type $ getParam $ numType herbie)
                    )
                    fromRationalDict
                )
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

----------------------------------------
-- get information from the environment

-- | Converts a String that contains a name of a variable into the compiler's internal representation of that variable.
getNameParent :: ModGuts -> String -> (Name,Parent)
getNameParent guts str = case filter isCorrectVar (concat $ occEnvElts (mg_rdr_env guts)) of
    xs -> if length xs>0
        then (gre_name $ head $ xs, gre_par $ head $ xs)
        else error $ "getNameParent: '"++str++"'\n"
    where
        isCorrectVar x = (getString $ gre_name x) == str
                      && (case gre_par x of NoParent -> False; _ -> True)

-- | Converts a string into a Core variable
getVar :: ModGuts -> String -> CoreM Var
getVar guts opstr = do
    let opname = fst $ getNameParent guts opstr
    hscenv <- getHscEnv
    dflags <- getDynFlags
    eps <- liftIO $ hscEPS hscenv
    let optype = case lookupNameEnv (eps_PTE eps) opname of
            Just (AnId i) -> varType i
    return $ mkGlobalVar VanillaId opname optype vanillaIdInfo

-- | Given a function name and concrete type, get the needed dictionary.
getDictConcrete :: ModGuts -> String -> Type -> CoreM (Maybe (Expr CoreBndr))
getDictConcrete guts opstr t = do
    hscenv <- getHscEnv
    dflags <- getDynFlags
    eps <- liftIO $ hscEPS hscenv
    let (opname,ParentIs classname) = getNameParent guts opstr
        classType = mkTyConTy $ case lookupNameEnv (eps_PTE eps) classname of
            Just (ATyCon t) -> t
            Just (AnId     _) -> error "loopupNameEnv AnId"
            Just (AConLike _) -> error "loopupNameEnv AConLike"
            Just (ACoAxiom _) -> error "loopupNameEnv ACoAxiom"
            Nothing           -> error "getNameParent gutsEnv Nothing"

        dictType = mkAppTy classType t
        dictVar = mkGlobalVar
            VanillaId
            (mkSystemName (mkUnique 'z' 1337) (mkVarOcc $ "magicDictionaryName"))
            dictType
            vanillaIdInfo

    bnds <- runTcM guts $ do
        loc <- getCtLoc $ GivenOrigin UnkSkol
        let nonC = mkNonCanonical $ CtWanted
                { ctev_pred = dictType
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

getDictPolymorphic :: ModGuts -> String -> ParamType -> CoreM (Maybe (Expr (CoreBndr)))
getDictPolymorphic guts opstr pt = do
    let (f,ParentIs p) =  getNameParent guts opstr
        c = case filter
            (\x -> getOccName x == nameOccName p)
            (concatMap getSuperClasses $ getClasses pt)
            of
          (x:_) -> x
          [] -> error $ "getDictPolymorphic: could not find parent"
            ++"\n  ; opstr="++opstr
            ++"\n  ; f="++occNameString (nameOccName f)
            ++"\n  ; p="++occNameString (nameOccName p)
            ++"\n  ; superclasses="++show (map getString $ concatMap getSuperClasses $ getClasses pt)
    dictFromParamType c pt

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
        go i (Var v) = "Var "++showSDoc dflags (ppr v)++"::"++showSDoc dflags (ppr $ varType v)
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
        go i (Case a b c d)
            = "Case\n"
            ++white++"("++go (i+1) a++")\n"
            ++white++"("++show b++"::"++showSDoc dflags (ppr $ varType b)++")\n"
            ++white++"("++showSDoc dflags (ppr c)++")\n"
            ++white++"["++concatMap (myAltShow dflags) d++"]\n"
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

myCoercionShow :: DynFlags -> Coercion -> String
myCoercionShow dflags c = go c
    where
        go (Refl _ _            ) = "Refl"
        go (TyConAppCo a b c    ) = "TyConAppCo "++showSDoc dflags (ppr a)++" "
                                                 ++showSDoc dflags (ppr b)++" "
                                                 ++showSDoc dflags (ppr c)
        go (AppCo _ _           ) = "AppCo"
        go (ForAllCo _ _        ) = "ForAllCo"
        go (CoVarCo _           ) = "CoVarCo"
        go (AxiomInstCo _ _ _   ) = "AxiomInstCo"
        go (UnivCo _ _ _ _      ) = "UnivCo"
        go (SymCo _             ) = "SymCo"
        go (TransCo _ _         ) = "TransCo"
        go (AxiomRuleCo _ _ _   ) = "AxiomRuleCo"
        go (NthCo _ _           ) = "NthCo"
        go (LRCo _ _            ) = "LRCo"
        go (InstCo _ _          ) = "InstCo"
        go (SubCo _             ) = "SubCo"

myAltShow :: DynFlags -> Alt Var -> String
-- myAltShow dflags (con,xs,expr) = "("++con'++", "++xs'++", "++myshow dflags expr++")"
myAltShow dflags (con,xs,expr) = "("++con'++", "++xs'++", BLAH)"
    where
        con' = case con of
            DataAlt x -> showSDoc dflags (ppr x)
            LitAlt x  -> showSDoc dflags (ppr x)
            DEFAULT   -> "DEFAULT"

        xs' = showSDoc dflags (ppr xs)

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


