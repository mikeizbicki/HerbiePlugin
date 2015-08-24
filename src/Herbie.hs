{-# LANGUAGE FlexibleInstances,FlexibleContexts,TemplateHaskell #-}
module Herbie
    ( plugin
    )
    where

import DsBinds
import DsMonad
import ErrUtils
import GhcPlugins
import Unique
import MkId
import TcRnMonad
import TcSimplify
-- import HERMIT.Dictionary.GHC
-- import HERMIT.Monad hiding (getHscEnv)

import Language.Haskell.TH (mkName)
import Data.List
import Data.Maybe
import System.Process

import Debug.Trace

--------------------------------------------------------------------------------
-- GHC plugin interface

plugin :: Plugin
plugin = defaultPlugin
    { installCoreToDos = install
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
    reinitializeGlobals
    return (CoreDoPluginPass "Herbie" pass : todo)

pass :: ModGuts -> CoreM ModGuts
pass guts = do
    bindsOnlyPass (mapM (modBind guts)) guts

modBind :: ModGuts -> CoreBind -> CoreM CoreBind
modBind guts bndr@(NonRec b e) = do
    dflags <- getDynFlags
    putMsgS $ "Non-recursive binding named " ++ showSDoc dflags (ppr b)
    e' <- modExpr guts e
    return $ NonRec b e'
--     return $ NonRec b e
modBind _ bndr = return bndr

modExpr :: ModGuts -> Expr Var -> CoreM (Expr Var)
modExpr guts e = do
    dflags <- getDynFlags
    let herbie = expr2herbie dflags e
    case hexpr herbie of
        ELeaf e -> case e of
            Lam a b -> do
                b' <- modExpr guts b
                return $ Lam a b'
--             App a b -> do
--                 a' <- modExpr guts a
--                 b' <- modExpr guts b
--                 return $ App a' b'
            Let a b -> do
                b' <- modExpr guts b
                return $ Let a b'
            otherwise -> do
--                 putMsgS $ "  not mathexpr: " ++ showSDoc dflags (ppr e)
                return e
        otherwise -> do
            putMsgS $ "  before (lisp): "++herbie2lisp dflags herbie
--             putMsgS $ "  before (core): "++showSDoc dflags (ppr e)
--             putMsgS $ "  before (raw ): "++myshow dflags e
            putMsgS $ ""
            herbie' <- callHerbie guts e herbie
            e' <- herbie2expr herbie'
            putMsgS $ "  after  (lisp): "++herbie2lisp dflags herbie'
--             putMsgS $ "  after  (core): "++showSDoc dflags (ppr e')
--             putMsgS $ "  after  (raw ): "++myshow dflags e'
            putMsgS $ ""
            return e'

--------------------------------------------------------------------------------
-- utils

var2str :: Var -> String
var2str = occNameString . occName . varName

maybeHead :: [a] -> Maybe a
maybeHead (a:_) = Just a
maybeHead _     = Nothing

--------------------------------------------------------------------------------
-- convert Expr into HerbieExpr

data Herbie = Herbie
    { hexpr :: HerbieExpr
    , binOpType :: Maybe Type
    , monOpType :: Maybe Type
    , numType :: Type
    , getExprs :: [(String,Expr Var)]
    }

herbie2cmd :: DynFlags -> Herbie -> String
herbie2cmd dflags herbie = "(herbie-test "++varStr++" \"cmd\" "++herbie2lisp dflags herbie++" )\n"
    where
        varStr = "(" ++ intercalate " " (map fst (getExprs herbie)) ++ ")"

herbie2expr :: Herbie -> CoreM (Expr Var)
herbie2expr = herbieExpr2expr . hexpr

herbie2lisp :: DynFlags -> Herbie -> String
herbie2lisp dflags herbie = herbieExpr2lisp dflags (hexpr herbie)

findExpr :: Herbie -> String -> Maybe (Expr Var)
findExpr herbie str = lookup str (getExprs herbie)

----------------------------------------

data HerbieExpr
    = EBinOp Var Type Var HerbieExpr HerbieExpr
    | EMonOp Var Type Var HerbieExpr
    | ELit Rational
    | ELeaf (Expr Var)

herbieExpr2lisp :: DynFlags -> HerbieExpr -> String
herbieExpr2lisp dflags = go
    where
        go (EBinOp op _ _ a1 a2) = "("++var2str op++" "++go a1++" "++go a2++")"
        go (EMonOp op _ _ a) = "("++var2str op++" "++go a++")"
        go (ELit r) = show (fromRational r::Double)
        go (ELeaf e) = expr2str dflags e

expr2str :: DynFlags -> Expr Var -> String
expr2str dflags (Var v) = {-"var_" ++-} var2str v
expr2str dflags e       = "expr_" ++ (decorate $ showSDoc dflags (ppr e))
    where
        decorate :: String -> String
        decorate = map go
            where
                go ' ' = '_'
                go '@' = '_'
                go '$' = '_'
                go x   = x

herbieExpr2expr :: HerbieExpr -> CoreM (Expr Var)
herbieExpr2expr h = go h
    where
        go (EBinOp op t dict a1 a2) = do
            a1' <- go a1
            a2' <- go a2
            return $ App (App (App (App (Var op) (Type t)) (Var dict)) a1') a2'
        go (EMonOp op t dict a) = do
            a' <- go a
            return $ App (App (App (Var op) (Type t)) (Var dict)) a'
        go (ELit r) = return $ mkConApp floatDataCon [mkFloatLit r]
        go (ELeaf e) = return e

expr2herbie :: DynFlags -> Expr Var -> Herbie
expr2herbie dflags e = Herbie hexpr (maybeHead bintypes) (maybeHead montypes) (getType e) exprs
    where
        (hexpr,bintypes,montypes,exprs) = go e [] [] []

        go :: Expr Var
           -> [Type]
           -> [Type]
           -> [(String,Expr Var)]
           -> (HerbieExpr,[Type],[Type],[(String,Expr Var)])

        -- we need to special case the $ operator for when HerbieExpr is run before any rewrite rules
        go e@(App (App (App (App (Var v) (Type _)) (Type _)) a1) a2) bins mons exprs
            = if var2str v == "$"
                then go (App a1 a2) bins mons exprs
                else (ELeaf e,bins,mons, [(expr2str dflags e,e)])

        -- all binary operators have this form
        go e@(App (App (App (App (Var v) (Type _)) (Var dict)) a1) a2) bins mons exprs
            = if var2str v `elem` binOpList
                then let (a1',bins1,mons1,exprs1) = go a1 [] [] []
                         (a2',bins2,mons2,exprs2) = go a2 [] [] []
                         t = varType v
                     in ( EBinOp v t dict a1' a2'
                        , t:bins++bins1++bins2
                        , mons++mons1++mons2
                        , (var2str v,Var dict):exprs++exprs1++exprs2
                        )
                else (ELeaf e,bins,mons,[(expr2str dflags e,e)])

        -- all unary operators have this form
        go e@(App (App (App (Var v) (Type _)) (Var dict)) a) bins mons exprs
            = if var2str v `elem` monOpList
                then let (a',bins',mons',exprs') = go a [] [] []
                         t = varType v
                     in ( EMonOp v t dict a'
                        , bins++bins'
                        , t:mons++mons'
                        , (var2str v, Var dict):exprs++exprs'
                        )
                else (ELeaf e,bins,mons,exprs)

        -- literals
        go e@(App (Var _) (Lit l)) bins mons exprs = (ELit r,bins,mons,exprs)
            where
                r = case l of
                    MachFloat r -> r
                    MachDouble r -> r

        -- everything else
        go e bins mons exprs = (ELeaf e,bins,mons,[(expr2str dflags e,e)])

-- | Determine the type of an expression.
-- FIXME: I have no idea if this is the correct way to do this, but it works :)
getType :: Expr Var -> Type
getType e = case go e of
    Just t -> t
    Nothing -> error "getType: couldn't determine type"
    where
        go (Type t) = Just t
        go (App a1 a2) = case go a1 of
            Just t -> Just t
            Nothing -> go a2
        go _ = Nothing

binOpList = [ "*", "/", "-", "+", "max", "min" ]
monOpList = [ "cos", "sin", "tan", "log", "sqrt" ]

--------------------------------------------------------------------------------
-- Herbie interface

data HerbieStr
    = SOp [HerbieStr]
    | SLeaf String
    deriving Show

-- | We just need to add spaces around the parens before calling "words"
tokenize :: String -> [String]
tokenize = words . concat . map go
    where
        go '(' = " ( "
        go ')' = " ) "
        go x   = [x]

-- | Assuming the previous token was a "(", splits the result into everything up until the matching ")" in fst, and everything after ")" in snd
findParen :: [String] -> ([String],[String])
findParen xs = go xs 0 []
    where
        go (")":xs) 0 left = (left,xs)
        go (")":xs) i left = go xs (i-1) (left++[")"])
        go ("(":xs) i left = go xs (i+1) (left++["("])
        go (x:xs)   i left = go xs i     (left++[x])

str2herbieStr :: String -> HerbieStr
str2herbieStr str = head $ go $ tokenize str
    where
        go ("(":xs) = SOp (go left):go right
            where
                (left,right) = findParen xs
        go (x:xs) = SLeaf x:go xs
        go [] = []

herbieStr2herbieExpr :: ModGuts -> Herbie -> HerbieStr -> CoreM HerbieExpr
herbieStr2herbieExpr guts herbie = go
    where
--         lookupNameParent str = case lookupOccEnv (mg_rdr_env guts) (mkVarOcc str) of
--             Just (x:[]) -> (gre_name x, gre_par x)
--             _ -> error $ "lookupNameParent "++str++" failed."
--             _ -> case filter isCorrectVar (concat $ occEnvElts (mg_rdr_env guts)) of
            -- Sometimes lookupOccEnv doesn't find a variable even though it exists in (mg_rdr_env guts).
            -- I don't know why this happens.
            -- But this is why we need the case below.
        lookupNameParent str = case filter isCorrectVar (concat $ occEnvElts (mg_rdr_env guts)) of
                xs -> (gre_name $ head $ xs, gre_par $ head $ xs)
                where
                    isCorrectVar x = (occNameString $ nameOccName $ gre_name x) == str
                                  && (case gre_par x of NoParent -> False; _ -> True)

        getVar opstr = do
            let opname = fst $ lookupNameParent opstr
            hscenv <- getHscEnv
            dflags <- getDynFlags
            eps <- liftIO $ hscEPS hscenv
            let optype = case lookupNameEnv (eps_PTE eps) opname of
                    Just (AnId i) -> varType i
            return $ mkGlobalVar VanillaId opname optype vanillaIdInfo

        getDict opstr = do
            hscenv <- getHscEnv
            dflags <- getDynFlags
            eps <- liftIO $ hscEPS hscenv
            let (opname,ParentIs classname) = lookupNameParent opstr
                classType = mkTyConTy $ case lookupNameEnv (eps_PTE eps) classname of
                    Just (ATyCon t) -> t
                    Just (AnId     _) -> error "loopupNameEnv AnId"
                    Just (AConLike _) -> error "loopupNameEnv AConLike"
                    Just (ACoAxiom _) -> error "loopupNameEnv ACoAxiom"
                    Nothing           -> error "lookupNameParentEnv Nothing"

                dictType = mkAppTy classType (numType herbie)
                dictVar = mkGlobalVar
                    VanillaId
                    (mkSystemName (mkUnique 'z' 76128) (mkVarOcc "herbie_magicvar"))
                    dictType
                    vanillaIdInfo

--             liftIO $ do
--                 putStrLn $ "eps_PTE="++showSDoc dflags (ppr $ eps_PTE eps)
--                 putStrLn ""
--                 putStrLn $ "opstr="++show opstr
--                 putStrLn $ "className="++showSDoc dflags (ppr classname)
--                 putStrLn $ "classType="++showSDoc dflags (ppr classType)
--                 putStrLn $ "dictType="++showSDoc dflags (ppr dictType)
--                 putStrLn $ "dictVar="++showSDoc dflags (ppr dictVar)

            bnds <- runTcM guts $ do
                loc <- getCtLoc $ GivenOrigin UnkSkol
                let nonC = mkNonCanonical $ CtWanted
                        { ctev_pred = dictType
                        , ctev_evar = dictVar
                        , ctev_loc = loc
                        }
                    wCs = mkSimpleWC [nonC]
--                 (x, evBinds) <- solveWantedsTcM wCs
                evBinds <- simplifyTop wCs
                bnds <- initDsTc $ dsEvBinds evBinds
--                 liftIO $ do
--                     putStrLn $ "nonC="++showSDoc dflags (ppr nonC)
--                     putStrLn $ "wCs="++showSDoc dflags (ppr wCs)
--                     putStrLn $ "evBinds="++showSDoc dflags (ppr bnds)
--                     putStrLn $ "bnds="++showSDoc dflags (ppr bnds)
--                     putStrLn $ "x="++showSDoc dflags (ppr x)
                return bnds
--             bnds <- runTcM guts . initDsTc $ dsEvBinds xs
            return $ case bnds of
                [NonRec _ (Var dict)] -> dict
                [] -> --error "no bnds"
                    case findExpr herbie opstr of
                        Just (Var v) -> v
--             error $ "getDict done " ++ showSDoc dflags (ppr dictType)

--             case findExpr herbie opstr of
--                 Just (Var v) -> return v
--                 Nothing -> do
--                     let opname = fst $ lookupNameParent "max"
--                     dflags <- getDynFlags
--                     hscenv <- getHscEnv
--                     eps <- liftIO $ hscEPS hscenv
--                     case lookupNameParentEnv (eps_PTE eps) opname of
--                         Just (AnId v) -> return v
--                         Just (AConLike _) -> error "loopupNameEnv AConLike"
--                         Just (ATyCon   _) -> error "loopupNameEnv ATyCon"
--                         Just (ACoAxiom _) -> error "loopupNameEnv ACoAxiom"
--                         Nothing           -> error "lookupNameParentEnv Nothing"

        {-
            let opname = lookupNameParent opstr
            hscenv <- getHscEnv
            dflags <- getDynFlags
            eps <- liftIO $ hscEPS hscenv
--             let opvar = case lookupNameParentEnv (eps_PTE eps) opname of
--                     Just (AnId v) -> v
            let opvar = case findExpr herbie opstr of
                    Just (Var v) -> v
            (x,xs) <- runTcM guts $ do
                loc <- getCtLoc $ GivenOrigin UnkSkol
                return undefined
                let predTy = varType opvar
                    nonC = mkNonCanonical $ CtWanted
                        { ctev_pred = predTy
                        , ctev_evar = opvar
                        , ctev_loc = loc
                        }
                    wCs = mkSimpleWC [nonC]
                (_, bnds) <- solveWantedsTcM wCs
                return (opvar, bnds)
            bnds <- runTcM guts . initDsTc $ dsEvBinds xs
            liftIO $ do
                putStrLn $ "(mg_rdr_env guts)="++showSDoc dflags (ppr (mg_rdr_env guts))
                putStrLn $ "x="++showSDoc dflags (ppr x)
                putStrLn $ "xs="++showSDoc dflags (ppr xs)
--             error "done"
            return $ case findExpr herbie opstr of
                Just (Var v) -> v
        -}

        ----------------------------------------
        -- recursion loop

        go (SLeaf str) = return $ case readMaybe str :: Maybe Double of
            Just d  -> ELit $ toRational d --ELeaf $ mkConApp floatDataCon [mkFloatLit $ toRational d]
            Nothing -> ELeaf $ case findExpr herbie str of
                Just x -> x
                Nothing -> error $ "herbieStr2herbieExpr: var " ++ str ++ " not in scope"

        go (SOp [SLeaf opstr, a1, a2]) = do
            a1' <- go a1
            a2' <- go a2
            var <- getVar opstr
            dict <- getDict opstr
            return $ EBinOp var (numType herbie) dict a1' a2'

        go (SOp [SLeaf opstr, a]) = do
            a' <- go a
            var <- getVar opstr
            dict <- getDict opstr
            return $ EMonOp var (numType herbie) dict a'

        go xs = error $ "herbieStr2herbieExpr: expr arity not supported: "++show xs

{-
        getVar opstr = do
            let opname = lookupNameParent opstr
--                 tbin = case binOpType herbie of
--                     Just x  -> x
--                     Nothing -> error "BinOp in Herbie output, but not original expression"
--                 dict = case findExpr herbie opstr of
--                     Just (Var v) -> v
--                     otherwise    -> mkGlobalVar VanillaId (lookupNameParent "fNumFloat") tbin vanillaIdInfo
-- --                     otherwise -> case lookupGRE_RdrName (mkRdrUnqual $ mkVarOcc "log") (mg_rdr_env guts) of
-- --                         (x:_) -> error "xxx"
-- --                         _     -> error $ "dictionary not found for: "++opstr

            hscenv <- getHscEnv
            dflags <- getDynFlags
            (ty,dict) <- liftIO $ do
                eps <- hscEPS hscenv
                let i = case lookupNameParentEnv (eps_PTE eps) opname of
                        Just (AnId i) -> i
                        otherwise -> error $ "herbieStr2herbieExpr: operator "++opstr++" not in scope"
                    t = varType i
--
                let (ClassPred c [tvar]) = classifyPredType $ snd . splitAppTy . fst . splitAppTy $ dropForAlls t
--                     dict' = mkDictSelId (varName $ getTyVar "panic" tvar) c -- dflags dflags -- True n' c :: Id
                    dict' = mkDictSelId opname c -- dflags dflags -- True n' c :: Id
--                     dict' = undefined -- mkDictSelId ( c -- dflags dflags -- True n' c :: Id
--
                putStrLn $ "------------ binup -- " ++ showSDoc dflags (ppr c)
                putStrLn $ "------------ binup -- " ++ showSDoc dflags (ppr tvar)
--
                return (t,dict')

            return (mkGlobalVar VanillaId opname ty vanillaIdInfo,dict)
            -}

callHerbie :: ModGuts -> Expr Var -> Herbie -> CoreM Herbie
callHerbie guts expr herbie = do
    dflags <- getDynFlags
    let lispstr = herbie2lisp dflags herbie
    lispstr' <- liftIO $ execHerbie lispstr
    hexpr' <- herbieStr2herbieExpr guts herbie $ str2herbieStr $ lispstr'
    return $ herbie
        { hexpr = hexpr'
        }

execHerbie :: String -> IO String
execHerbie lisp = do
    let vars = nub
             $ sort
             $ filter (\x -> x/="("
                          && x/=")"
                          && not (x `elem` binOpList)
                          && not (x `elem` monOpList)
                          && not (head x `elem` "1234567890")
                      ) $ tokenize lisp :: [String]
        varstr = "("++(intercalate " " vars)++")"
        cmd = "(herbie-test "++varstr++" \"cmd\" "++lisp++") \n"
--     putStrLn $ "cmd="++show cmd
    (_,stdout,stderr) <- readProcessWithExitCode "herbie-exec" [] cmd
--     putStrLn $ "stdout="++show stdout
--     putStrLn $ "stderr="++show stderr
    let lisp' = dropWhile (/='(')
              $ drop 1
              $ dropWhile (/='(')
              $ drop 1
              $ dropWhile (/='(')
              $ take (length stdout-2)
              $ stdout
--     putStrLn $ "lisp'="++show lisp'
--     putStrLn ""
    return lisp'

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

readMaybe :: Read a => String -> Maybe a
readMaybe = fmap fst . listToMaybe . reads

--------------------------------------------------------------------------------
-- debugging

myshow :: DynFlags -> Expr Var -> String
myshow dflags (Var v) = "Var "++showSDoc dflags (ppr v)++"::'"++showSDoc dflags (ppr $ varType v)++"'"
myshow dflags (Lit l) = "Lit"
myshow dflags (Type t) = "Type "++showSDoc dflags (ppr t)
myshow dflags (Coercion l) = "Coercion"
myshow dflags (App a b) = "App (" ++ myshow dflags a ++ ") ("++myshow dflags b++")"
myshow dflags (Lam a b) = "Lam (" ++ show a ++ ") ("++myshow dflags b++")"
myshow dflags (Let a b) = "Let (" ++ show a ++ ") ("++myshow dflags b++")"
myshow dflags (Cast a b) = "Case (" ++ myshow dflags a ++ ") ("++show b++")"
myshow dflags (Tick a b) = "Tick (" ++ show a ++ ") ("++myshow dflags b++")"
myshow dflags (Case a b c d) = "Case ("++myshow dflags a++") ("++show b++") ("++show c++") (LISTOFJUNK)"
-- myshow dflags (Case a b c d) = "Case ("++myshow dflags a++") ("++show b++") ("++show c++") ("++myshow dflags d++")"

instance Show (Coercion) where
    show _ = "Coercion"

instance Show b => Show (Bind b) where
    show _ = "Bind"

instance Show (Tickish Id) where
    show _ = "(Tickish Id)"

instance Show Type where
    show _ = "Type"

instance Show AltCon where
    show _ = "AltCon"

instance Show Var where
    show v = "name"


