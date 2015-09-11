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

import Control.Monad
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
            cond' <- go cond >>= castToType (getDicts pt) boolTy
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

                where
                    castToType :: [Var] -> Type -> CoreExpr -> CoreM CoreExpr
                    castToType preds castTy expr = if exprType expr == castTy
                        then return expr
                        else do
                            coboxUniq <- getUniqueM
                            let coboxName = mkSystemName coboxUniq (mkVarOcc $ "cobox")
                                coboxType = mkCoercionType Nominal (exprType expr) castTy
                                coboxVar = mkLocalVar VanillaId coboxName coboxType vanillaIdInfo

                            let eqpred = head $ filter go preds
                                    where
                                        go pred = case classifyPredType $ varType pred of
                                            EqPred _ _ _ -> True
                                            _ -> False
                                coercion = mkSubCo $ mkCoVarCo coboxVar

                            wildUniq <- getUniqueM
                            let wildName = mkSystemName wildUniq (mkVarOcc $ "wild")
                                wildType = varType eqpred
                                wildVar = mkLocalVar VanillaId wildName wildType vanillaIdInfo

                            return $ Case
                                (Var eqpred)
                                wildVar
                                castTy
                                [ (DataAlt eqBoxDataCon, [coboxVar], Cast expr coercion) ]

-- Lam a_a608::*; coercion=False
-- (Lam $dBoolean_a60j::Boolean (Logic a); coercion=False
-- (Lam $dLattice__a60k::Lattice_ a; coercion=False
-- (Lam $dSemigroup_a60l::Semigroup a; coercion=False
-- (Lam cobox_a60m::Logic a ~ Bool; coercion=False
-- (Let cobox_a60t::Bool ~ Logic a
-- (Let $dComplemented_a60s::Complemented (Logic a)
-- (Let $dPOrd__a60r::POrd_ a
-- (Lam x_a2H2::a; coercion=False
-- (Lam y_a2H3::a; coercion=False
-- (Case
--     (Case
--         (Var cobox_a60t_a60t::Bool ~ Logic a)
--         (cobox_X60F::Bool ~ Logic a)
--         (Bool)
--         [(Eq#, ["Var cobox_d62x::Bool ~# Logic a"], Cast
--             (App
--                 (App
--                     (App
--                         (App
--                             (App
--                                 (Var <_r3b::forall b. (POrd_ b, Complemented (Logic b)) => b -> b -> Logic b)
--                                 (Type a)
--                             )
--                             (Var $dPOrd__a60r_a60r::POrd_ a)
--                         )
--                         (Var $dComplemented_a60s_a60s::Complemented (Logic a))
--                     )
--                     (Var x_a2H2::a)
--                 )
--                 (Var y_a2H3::a)
--             )
--             (Coercion SubCo (SymCo (CoVarCo (Var cobox_d62x::Bool ~# Logic a))))
--         )
--         ]
--     )
--     (wild_00::Bool)
--     (a)
--     [(False, [], Var y_a2H3::a)
--     (True, [], Var x_a2H2::a)
--     ]

        -- leaf is a numeric literal
        go (ELit r) = do
            fromRationalExpr <- getDecoratedFunction guts "fromRational" (getParam pt) (getDicts pt)

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
    let ([v],unquantified) = extractQuantifiers $ varType f
        (cxt,_) = extractContext unquantified
        cxt' = substTysWith [v] [t] cxt

    cxt'' <- fmap concat $ mapM getDict cxt'

    return $ mkApps (App (Var f) (Type t)) cxt''
    where
        getDict :: PredType -> CoreM [CoreExpr]
        getDict pred = do
            ret <- getDictionary guts pred
            case ret of
                Just x -> return [x]
                Nothing -> do
                    ret <- getPredEvidence pred (map Var preds)
                    case ret of
                        Just x -> return [x]
                        Nothing -> error $ "getDict: f="++getString f++"; pred="++showSDoc dynFlags (ppr pred)

-- | Given a predicate for which we don't have evidence
-- and a list of expressions that contain evidence for predicates,
-- construct an expression that contains evidence for the given predicate.
getPredEvidence :: PredType -> [CoreExpr] -> CoreM (Maybe CoreExpr)
getPredEvidence pred xs = go [ (x, extractBaseTy $ exprType x) | x <- xs ]
    where
        -- Extracts the type that each of our pieces of evidence is applied to
        extractBaseTy :: Type -> Type
        extractBaseTy t = case classifyPredType t of
            ClassPred _ [x] -> x
            EqPred rel t1 t2 -> error $ "EqPred: rel="++dbg rel
                                        ++"; t1="++dbg t1
                                        ++"; t2="++dbg t2


        -- Recursively descend into all the available predicates.
        -- The list tracks both the evidence expression (this will change in recursive descent),
        -- and the baseTy that gave rise to the expression (this stays constant).
        go :: [(CoreExpr,Type)] -> CoreM (Maybe (CoreExpr))
        go []                    = return Nothing
        go ((expr,baseTy):exprs) = if exprType expr == pred

            -- The expression we've found matches the predicate.
            -- We're done!
            then return $ Just expr

            -- The expression doesn't match the predicate,
            -- so we recurse by searching for sub-predicates within expr
            -- and adding them to the list.
            else case classifyPredType (exprType expr) of

                -- What we've found contains no more predicates to recurse into,
                -- so we don't add anything to the list of exprs to search.
                IrredPred _ ->
--                     trace ("getPredEvidence.go.IP: pred="++dbg pred++"; exprType="++dbg (exprType expr)) $
                    go exprs
                EqPred _ _ _ ->
--                     trace ("getPredEvidence.go.EP: pred="++dbg pred++"; exprType="++dbg (exprType expr)) $
                    go exprs

                -- We've found a class dictionary.
                -- Recurse into each field (selId) of the dictionary.
                -- Some (but not all) of these may be more dictionaries.
                ClassPred c' [ct] -> trace ("getPredEvidence.go.CP: pred="++dbg pred
                                        ++"; origType="++dbg (baseTy)
                                        ++"; exprType="++dbg (exprType expr)
                                        ) $
                  go $
                    exprs++
                    [ ( App (App (Var selId) (Type baseTy)) expr
                      , baseTy
                      )
                    | selId <- classAllSelIds c'
                    ]
--                     where
--                         -- The predicate we're inspecting might be acting on
--                         -- something more complicated than just a type variable.
--                         -- For example, the predicate might be `Boolean (Logic a)`
--                         -- instead of just `Boolean a`.
--                         -- This function ensures that any type constructors in the predicate
--                         -- get propagated correctly into the selId's.
--                         applyTypeConstructors :: Type -> Type
--                         applyTypeConstructors t = mkForAllTy v $ substTyWith [v] [unk'] unquantified
--                             where
--                                 unk' = substTyWith
--                                     [predArgTyVar]
--                                     [mkTyVarTy v]
--                                     unk
--
--                                 (tyCon,unk) = splitAppTy pred
--                                 ([v],unquantified) = extractQuantifiers t

                -- We've found a tuple of evidence.
                -- For each field of the tuple we extract it with a case statement, then recurse.
                TuplePred preds -> do
                    trace ("getPredEvidence.go.TP: pred="++dbg pred
                                        ++"; origType="++dbg (baseTy)
                                        ++"; exprType="++dbg (exprType expr)
                                        ) $ return ()

                    uniqs <- getUniquesM
                    let tupelems =
                            [ mkLocalVar
                                VanillaId
                                (mkSystemName uniq (mkVarOcc $ "a"++show j))
                                (mkAppTy (fst $ splitAppTys t') baseTy)
                                vanillaIdInfo
                            | (j,t',uniq) <- zip3 [0..] preds uniqs
                            ]

                    uniq <- getUniqueM
                    let wildName = mkSystemName uniq (mkVarOcc $ "wild")
                        wildVar = mkLocalVar VanillaId wildName (exprType expr) vanillaIdInfo

                    let ret =
                            [ ( Case expr wildVar (varType $ tupelems!!i)
                                [ ( DataAlt $ tupleCon ConstraintTuple $ length preds
                                  , tupelems
                                  , Var $ tupelems!!i
                                  )
                                ]
                              , baseTy
                              )
                            | (i,t) <- zip [0..] preds
                            ]

                    go $ ret++exprs

-- | Return all the TyVars that occur anywhere in the Type
extractTyVars :: Type -> [TyVar]
extractTyVars t = case getTyVar_maybe t of
    Just x -> [x]
    Nothing -> case tyConAppArgs_maybe t of
        Just xs -> concatMap extractTyVars xs
        Nothing -> concatMap extractTyVars $ snd $ splitAppTys t

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
                     ++"_"++showSDoc dflags (ppr $ getUnique v)
                     ++"::"++showSDoc dflags (ppr $ varType v)
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
            = "Let "++getString a++"_"++showSDoc dflags (ppr $ getUnique a)
                                ++"::"++showSDoc dflags (ppr $ varType a)++"\n"
            ++white++"("++go (i+1) b++")\n"
            ++drop 4 white
            where
                white=replicate (4*i) ' '
        go i (Let _ _) = error "myshow: recursive let"
        go i (Lam a b)
            = "Lam "++getString a++"_"++showSDoc dflags (ppr $ getUnique a)
                                ++"::"++showSDoc dflags (ppr $ varType a)
                                ++"; coercion="++show (isCoVar a)++"\n"
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
            ++white++"("++getString b++"_"++showSDoc dflags (ppr $ getUnique b)
                                    ++"::"++showSDoc dflags (ppr $ varType b)++")\n"
            ++white++"("++showSDoc dflags (ppr c)++"; "++show (fmap (myshow dflags . Var) $ getTyVar_maybe c)++")\n"
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

                        xs' = show $map (myshow dflags . Var) xs

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


