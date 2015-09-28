{-# LANGUAGE CPP #-}
module Herbie.CoreManip
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

import Herbie.MathExpr

import Prelude
import Show

-- import Debug.Trace hiding (traceM)
trace a b = b
traceM a = return ()

--------------------------------------------------------------------------------

instance MonadUnique m => MonadUnique (ExceptT e m) where
    getUniqueSupplyM = lift getUniqueSupplyM

instance (Monad m, HasDynFlags m) => HasDynFlags (ExceptT e m) where
    getDynFlags = lift getDynFlags

instance MonadThings m => MonadThings (ExceptT e m) where
    lookupThing name = lift $ lookupThing name

----------------------------------------
-- core manipulation

-- | Converts a string into a Core variable
getVar :: ModGuts -> String -> ExceptT String CoreM Var
getVar guts opstr = do
    let opname = getName guts opstr
    hscenv <- lift getHscEnv
    dflags <- getDynFlags
    eps <- liftIO $ hscEPS hscenv
    optype <- case lookupNameEnv (eps_PTE eps) opname of
            Just (AnId i) -> return $ varType i
            _ -> throwError $ "  WARNING: variable \""++opstr++"\" not in scope"
    return $ mkGlobalVar VanillaId opname optype vanillaIdInfo

    where
        getName :: ModGuts -> String -> Name
        getName guts str = case filter isCorrectVar (concat $ occEnvElts (mg_rdr_env guts)) of
            xs -> if not (null xs)
                then gre_name $ head xs
                else error $ "getName: '"++str++"'"
            where
                isCorrectVar x = getString (gre_name x) == str
                              && (str == "abs" || case gre_par x of NoParent -> False; _ -> True)

-- | Like "decorateFunction", but first finds the function variable given a string.
getDecoratedFunction :: ModGuts -> String -> Type -> [CoreExpr] -> ExceptT String CoreM CoreExpr
getDecoratedFunction guts str t preds = do
    f <- getVar guts str
    decorateFunction guts f t preds

-- | Given a variable that contains a function,
-- the type the function is being applied to,
-- and all in scope predicates,
-- apply the type and any needed dictionaries to the function.
decorateFunction :: ModGuts -> Var -> Type -> [CoreExpr] -> ExceptT String CoreM CoreExpr
decorateFunction guts f t preds = do
    let ([v],unquantified) = extractQuantifiers $ varType f
        (cxt,_) = extractContext unquantified
        cxt' = substTysWith [v] [t] cxt

    cxt'' <- mapM getDict cxt'

    return $ mkApps (App (Var f) (Type t)) cxt''
    where
        getDict :: PredType -> ExceptT String CoreM CoreExpr
        getDict pred = do
            catchError
                (getDictionary guts pred)
                (\_ -> getPredEvidence guts pred preds)

-- | Given a non-polymorphic PredType (e.g. `Num Float`),
-- return the corresponding dictionary.
getDictionary :: ModGuts -> Type -> ExceptT String CoreM CoreExpr
getDictionary guts dictTy = do
    let dictVar = mkGlobalVar
            VanillaId
            (mkSystemName (mkUnique 'z' 1337) (mkVarOcc "magicDictionaryName"))
            dictTy
            vanillaIdInfo

    bnds <- lift $ runTcM guts $ do
        loc <- getCtLoc $ GivenOrigin UnkSkol
        let nonC = mkNonCanonical CtWanted
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
        [NonRec _ dict] -> return dict
        otherwise -> throwError $
            "  WARNING: Cannot satisfy the constraint: "++dbg dictTy

-- | Given a predicate for which we don't have evidence
-- and a list of expressions that contain evidence for predicates,
-- construct an expression that contains evidence for the given predicate.
getPredEvidence :: ModGuts -> PredType -> [CoreExpr] -> ExceptT String CoreM CoreExpr
getPredEvidence guts pred evidenceExprs = go $ prepEvidence evidenceExprs
    where

        go :: [(CoreExpr,Type)] -> ExceptT String CoreM CoreExpr

        -- We've looked at all the evidence, but didn't find anything
        go [] = throwError $
            "  WARNING: Cannot satisfy the constraint: "++dbg pred

        -- Recursively descend into all the available predicates.
        -- The list tracks both the evidence expression (this will change in recursive descent),
        -- and the baseTy that gave rise to the expression (this stays constant).
        go ((expr,baseTy):exprs) = if exprType expr == pred

            -- The expression we've found matches the predicate.
            -- We're done!
            then return expr

            -- The expression doesn't match the predicate,
            -- so we recurse by searching for sub-predicates within expr
            -- and adding them to the list.
            else case classifyPredType (exprType expr) of

                -- What we've found contains no more predicates to recurse into,
                -- so we don't add anything to the list of exprs to search.
                IrredPred _ -> go exprs

                EqPred _ t1 t2 -> trace ("getPredEvidence.go.EP: pred="++dbg pred
                    ++"; origType="++dbg baseTy
                    ++"; exprType="++dbg (exprType expr)
                    ) $ case splitAppTy_maybe pred of
                        Nothing -> trace " A" $ go exprs
--                         Just (tyCon,tyApp) -> if baseTy/=tyApp
                        Just (tyCon,tyApp) -> trace " A'" $ if t1/=tyApp && t2 /=tyApp
                            then trace (" B: baseTy="++dbg baseTy++"; tyApp="++dbg tyApp)
                                $ go exprs
                            else do
                                let pred' = mkAppTy tyCon $ if t1==tyApp
                                        then t2
                                        else t1
                                getDictionary guts pred' >>= castToType evidenceExprs pred

                -- We've found a class dictionary.
                -- Recurse into each field (selId) of the dictionary.
                -- Some (but not all) of these may be more dictionaries.
                --
                -- FIXME: Multiparamter classes broken
                ClassPred c' [ct] -> trace ("getPredEvidence.go.CP: pred="++dbg pred
                                        ++"; origType="++dbg baseTy
                                        ++"; exprType="++dbg (exprType expr)
                                        ) $
                  go $
                    exprs++
                    [ ( App (App (Var selId) (Type baseTy)) expr
                      , baseTy
                      )
                    | selId <- classAllSelIds c'
                    ]

                ClassPred _ _ -> go exprs

                -- We've found a tuple of evidence.
                -- For each field of the tuple we extract it with a case statement, then recurse.
                TuplePred preds -> do
                    trace ("getPredEvidence.go.TP: pred="++dbg pred
                                        ++"; origType="++dbg baseTy
                                        ++"; exprType="++dbg (exprType expr)
                                        ) $ return ()

                    uniqs <- getUniquesM

                    traceM $ " tupelems: baseTy="++dbg baseTy++"; preds="++dbg preds
                    let tupelems =
                            [ mkLocalVar
                                VanillaId
                                (mkSystemName uniq (mkVarOcc $ "a"++show j))
                                t'
--                                 (mkAppTy (fst $ splitAppTys t') baseTy)
                                vanillaIdInfo
                            | (j,t',uniq) <- zip3 [0..] preds uniqs
                            ]

                    uniq <- getUniqueM
                    let wildName = mkSystemName uniq (mkVarOcc "wild")
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

                    sequence_ [ traceM $ "  ret!!"++show i++"="++myshow dynFlags (fst $ ret!!i) | i<-[0..length ret-1]]

                    go $ ret++exprs

-- | Given some evidence, an expression, and a type:
-- try to prove that the expression can be cast to the type.
-- If it can, return the cast expression.
castToType :: [CoreExpr] -> Type -> CoreExpr -> ExceptT String CoreM CoreExpr
castToType xs castTy inputExpr = if exprType inputExpr == castTy
    then return inputExpr
    else go $ prepEvidence xs
--     else go $ catMaybes [ (x, extractBaseTy $ exprType x) | x <- xs ]
    where


        go :: [(CoreExpr,Type)] -> ExceptT String CoreM CoreExpr

        -- base case: we've searched through all the evidence, but couldn't create a cast
        go [] = throwError $
            "  WARNING: Could not cast expression of type "++dbg (exprType inputExpr)++" to "++dbg castTy

        -- recursively try each evidence expression looking for a cast
        go ((expr,baseTy):exprs) = case classifyPredType $ exprType expr of

            IrredPred _ -> go exprs

            EqPred _ t1 t2 -> trace ("castToType.go.EP: castTy="++dbg castTy
              ++"; origType="++dbg baseTy
              ++"; exprType="++dbg (exprType expr)
              ) $ goEqPred [] castTy (exprType inputExpr)
                where
                    -- Check if a cast is possible.
                    -- We need to recursively peel off all the type constructors
                    -- on the inputTyRHS and castTyRHS types.
                    -- As long as the type constructors match,
                    -- we might be able to do a cast at any level of the peeling
                    goEqPred :: [TyCon] -> Type -> Type -> ExceptT String CoreM CoreExpr
                    goEqPred tyCons castTyRHS inputTyRHS = if
                        | t1==castTyRHS && t2==inputTyRHS -> mkCast True
                        | t2==castTyRHS && t1==inputTyRHS -> mkCast False
                        | otherwise -> case ( splitTyConApp_maybe castTyRHS
                                            , splitTyConApp_maybe inputTyRHS
                                            ) of
                            (Just (castTyCon, [castTyRHS']), Just (inputTyCon,[inputTyRHS'])) ->
                                if castTyCon == inputTyCon
                                    then goEqPred (castTyCon:tyCons) castTyRHS' inputTyRHS'
                                    else go exprs
                            _ -> go exprs
                        where

                            -- Constructs the actual cast from one variable type to another.
                            --
                            -- There's some subtle voodoo in here involving GHC's Roles.
                            -- Basically, everything gets created as a Nominal role,
                            -- but the final Coercion needs to be Representational.
                            -- mkSubCo converts from Nominal into Representational.
                            -- See https://ghc.haskell.org/trac/ghc/wiki/RolesImplementation
                            mkCast :: Bool -> ExceptT String CoreM CoreExpr
                            mkCast isFlipped = do
                                coboxUniq <- getUniqueM
                                let coboxName = mkSystemName coboxUniq (mkVarOcc "cobox")
                                    coboxType = if isFlipped
                                        then mkCoercionType Nominal castTyRHS inputTyRHS
                                        else mkCoercionType Nominal inputTyRHS castTyRHS
                                    coboxVar = mkLocalVar VanillaId coboxName coboxType vanillaIdInfo

                                -- Reapplies the list of tyCons that we peeled off during the recursion.
                                let mkCoercion [] = if isFlipped
                                        then mkSymCo $ mkCoVarCo coboxVar
                                        else mkCoVarCo coboxVar
                                    mkCoercion (x:xs) = mkTyConAppCo Nominal x [mkCoercion xs]

                                wildUniq <- getUniqueM
                                let wildName = mkSystemName wildUniq (mkVarOcc "wild")
                                    wildType = exprType expr
                                    wildVar = mkLocalVar VanillaId wildName wildType vanillaIdInfo

                                return $ Case
                                    expr
                                    wildVar
                                    castTy
                                    [ ( DataAlt eqBoxDataCon
                                      , [coboxVar]
                                      , Cast inputExpr $ mkSubCo $ mkCoercion tyCons
                                      ) ]

            -- | FIXME: ClassPred and TuplePred are both handled the same
            -- within castToPred and getPredEvidence.
            -- They should be factored out?
            ClassPred c' [ct] -> go $
                exprs++
                [ ( App (App (Var selId) (Type baseTy)) expr
                  , baseTy
                  )
                | selId <- classAllSelIds c'
                ]

            ClassPred _ _ -> go exprs

            TuplePred preds -> do
                uniqs <- getUniquesM
                let tupelems =
                        [ mkLocalVar
                            VanillaId
                            (mkSystemName uniq (mkVarOcc $ "a"++show j))
--                             (mkAppTy (fst $ splitAppTys t') baseTy)
                            t'
                            vanillaIdInfo
                        | (j,t',uniq) <- zip3 [0..] preds uniqs
                        ]

                uniq <- getUniqueM
                let wildName = mkSystemName uniq (mkVarOcc "wild")
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

-- | Each element in the input list must contain evidence of a predicate.
-- The output list contains evidence of a predicate along with a type that will be used for casting.
prepEvidence :: [CoreExpr] -> [(CoreExpr,Type)]
prepEvidence exprs = catMaybes
    [ case extractBaseTy $ exprType x of
        Just t -> Just (x,t)
        Nothing -> Nothing --(x, extractBaseTy $ exprType x)
    | x <- exprs
    ]

    where
        -- Extracts the type that each of our pieces of evidence is applied to
        extractBaseTy :: Type -> Maybe Type
        extractBaseTy t = case classifyPredType t of

            ClassPred _ [x] -> Just x

            EqPred rel t1 t2 -> if
                | t1 == boolTy -> Just t2
                | t2 == boolTy -> Just t1
                | otherwise -> Nothing

            _ -> Nothing

-- | Return all the TyVars that occur anywhere in the Type
extractTyVars :: Type -> [TyVar]
extractTyVars t = case getTyVar_maybe t of
    Just x -> [x]
    Nothing -> case tyConAppArgs_maybe t of
        Just xs -> concatMap extractTyVars xs
        Nothing -> concatMap extractTyVars $ snd $ splitAppTys t

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
    Just (tycon,xs) -> if occNameString (nameOccName $ tyConName tycon) /= "(->)"
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
    Just (tycon,xs) -> if occNameString (nameOccName $ tyConName tycon) /= "(->)"
        then Just t -- Nothing
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


--------------------------------------------------------------------------------
--

runTcM :: ModGuts -> TcM a -> CoreM a
runTcM guts tcm = do
    env <- getHscEnv
    dflags <- getDynFlags
#if __GLASGOW_HASKELL__ < 710 || (__GLASGOW_HASKELL__ == 710 && __GLASGOW_HASKELL_PATCHLEVEL1__ < 2)
    (msgs, mr) <- liftIO $ initTc env HsSrcFile False (mg_module guts) tcm
#else
    let realSrcSpan = mkRealSrcSpan
            (mkRealSrcLoc (mkFastString "a") 0 1)
            (mkRealSrcLoc (mkFastString "b") 2 3)
    (msgs, mr) <- liftIO $ initTc env HsSrcFile False (mg_module guts) realSrcSpan tcm
#endif
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
expr2str dflags e       = "expr_" ++ decorate (showSDoc dflags (ppr e))
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
            ++white++"("++go (i+1) e++")\n"
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

                        xs' = show $ map (myshow dflags . Var) xs

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


