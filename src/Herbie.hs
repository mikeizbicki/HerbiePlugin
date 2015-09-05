{-# LANGUAGE FlexibleInstances,FlexibleContexts,TemplateHaskell #-}
module Herbie
    ( plugin
    )
    where

import Class
import DsBinds
import DsMonad
import ErrUtils
import GhcPlugins
import Unique
import MkId
import TcRnMonad
import TcSimplify

import Language.Haskell.TH (mkName)
import Data.Char
import Data.List
import Data.Maybe
import System.Process

import Debug.Trace
import Show
import Data.IORef

--------------------------------------------------------------------------------
-- GHC plugin interface

plugin :: Plugin
plugin = defaultPlugin
    { installCoreToDos = install
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
    dflags <- getDynFlags
    liftIO $ writeIORef dynFlags_ref dflags
    reinitializeGlobals
    return (CoreDoPluginPass "Herbie" pass : todo)

pass :: ModGuts -> CoreM ModGuts
pass guts = do
    bindsOnlyPass (mapM (modBind guts)) guts

modBind :: ModGuts -> CoreBind -> CoreM CoreBind
modBind guts bndr@(Rec _) = return bndr
modBind guts bndr@(NonRec b e) = do
    dflags <- getDynFlags
    putMsgS $ "Non-recursive binding named "
        ++ showSDoc dflags (ppr b)
        ++ "::"
        ++ showSDoc dflags (ppr $ varType b)
    e' <- go [] e
    return $ NonRec b e'
    where
        go dicts e = do
            dflags <- getDynFlags
            let mparamtype = mkParamType dicts (varType b)
            case mparamtype of
                Nothing -> return e
                Just paramtype -> do
                    let herbie = expr2herbie dflags paramtype e
                    case hexpr herbie of
                        ELeaf e -> case e of
                            Lam a b -> do
--                               trace (" Lam a="++showSDoc dflags (ppr a)
--                                      ++" ; b="{-++showSDoc dflags (ppr b)-}
--                                      ++" ; dicts="++showSDoc dflags (ppr dicts)) $ do
                                let dicts' = if (head $ occNameString $ nameOccName $ varName a)=='$'
                                        then a:dicts
                                        else dicts
                                b' <- go dicts' b
                                return $ Lam a b'
                            Let a b -> do
--                             trace (" Let a="++showSDoc dflags (ppr a)
--                                    ++" ; b="{-++showSDoc dflags (ppr b)-})
                                b' <- go dicts b
                                return $ Let a b'
        --                  FIXME: handling math expressions within function applications is harder
        --                  because we have to figure out the type of the inner expression somehow
        --                     App a b -> do
        --                         a' <- modExpr guts a
        --                         b' <- modExpr guts b
        --                         return $ App a' b'
                            otherwise -> do
                                putMsgS $ "  not mathexpr: " ++ showSDoc dflags (ppr e)
                                return e
                        otherwise -> do
                            putMsgS $ "  before (lisp): "++herbie2lisp dflags herbie
                            putMsgS $ ""
--                             putMsgS $ "  before (core): "++showSDoc dflags (ppr e)
--                             putMsgS $ ""
--                             putMsgS $ "  before (raw ): "++myshow dflags e
--                             putMsgS $ "  before (raw ): "++show e
                            putMsgS $ ""
                            herbie' <- callHerbie guts e herbie
                            e' <- herbie2expr herbie'
                            putMsgS $ "  after  (lisp): "++herbie2lisp dflags herbie'
                            putMsgS $ ""
--                             putMsgS $ "  after  (core): "++showSDoc dflags (ppr e')
--                             putMsgS $ ""
--                             putMsgS $ "  after  (raw ): "++myshow dflags e'
--                             putMsgS $ "  after  (raw ): "++show e'
                            putMsgS $ ""
                            return e'

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

getDictMap :: ParamType -> [(Class,Expr Var)]
getDictMap pt = nubBy f $ go $ getDictMap0 pt
    where
        f (a1,_) (a2,_) = getString a1==getString a2

        go [] = []
        go (x@(c,dict):xs) = x:go (xs++xs')
            where
                xs' = concat $ map constraint2dictMap $ classSCTheta c

                constraint2dictMap t = case classifyPredType t of
                    ClassPred c' _ -> [(c',dict')]
                        where
                            dict' = mkApps (Var (findSelId c' (classAllSelIds c))) [Type $ getParam pt, dict]
                    _ -> []

-- | Given a list of member functions of a class,
-- return the function that extracts the dictionary corresponding to c.
findSelId :: Class -> [Var] -> Var
findSelId c [] = error "findSelId: this shouldn't happen"
findSelId c (v:vs) = if isDictSelector c v
    then v
    else findSelId c vs

-- | Returns a dictionary map for just the top level cxt of the ParamType.
-- This is used to seed getDictMap.
getDictMap0 :: ParamType -> [(Class,Expr Var)]
getDictMap0 pt = map f $ getClasses pt
    where
        f c = case filter (isDict c) $ getDicts pt of
            []  -> error $ "getDictMap: no dictionary for class "++getString c
            [x] -> (c,Var x)
            xs   -> error $ "getDictMap: multiple dictionaries for class "++getString c
                          ++": "++show (map getString xs)

-- | True only if dict is a dictionary for c
isDict :: Class -> Var -> Bool
isDict c dict = getString c == dropWhile go (getString dict)
    where
        go x = x=='$'||isLower x||isDigit x

-- | True only if dict is a dictionary selector for c
isDictSelector :: Class -> Var -> Bool
isDictSelector c dict = case classifyPredType $ getReturnType $ varType dict of
    ClassPred c' _ -> c==c'
    _ -> False

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
dictFromParamType c pt = do
    dflags <- getDynFlags
    let dm = getDictMap pt
--     putMsgS $ "getDictMap="++showSDoc dflags (ppr dm)
    return $ lookup c dm

--     error "poop"
--     cs <- getClasses pt
--     case filter (\(c',_) -> c'==c) cs of
--         [] -> error $ "dictFromParamType: no dict found for class "
--                      ++(occNameString $ nameOccName $ getName c)
--         [(_,dict)]-> return $ Just dict

--     mkApps (Var (head (classSCSels ord_class))) [Var ord_dictionary]

getClasses :: ParamType -> [Class]
getClasses pt = concat $ map go $ getCxt pt
    where
        go t = case classifyPredType t of
            ClassPred c _ -> [c]
            _ -> []

getSuperClasses :: Class -> [Class]
getSuperClasses c = c : (nub $ concat $ map getSuperClasses $ concat $ map go $ classSCTheta c)
    where
        go t = case classifyPredType t of
            ClassPred c _ -> [c]
            _ -> []

--------------------------------------------------------------------------------
-- utils

getString :: NamedThing a => a -> String
getString = occNameString . getOccName

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

--------------------------------------------------------------------------------
-- convert Expr into HerbieExpr

data Herbie = Herbie
    { hexpr :: HerbieExpr
    , binOpType :: Maybe Type
    , monOpType :: Maybe Type
    , numType :: ParamType
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
    = EBinOp Var Type (Expr Var) HerbieExpr HerbieExpr
    | EMonOp Var Type (Expr Var) HerbieExpr
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
            return $ App (App (App (App (Var op) (Type t)) dict) a1') a2'
        go (EMonOp op t dict a) = do
            a' <- go a
            return $ App (App (App (Var op) (Type t)) dict) a'
        go (ELit r) = return $ mkConApp floatDataCon [mkFloatLit r]
        go (ELeaf e) = return e

expr2herbie :: DynFlags -> ParamType -> Expr Var -> Herbie
expr2herbie dflags t e = Herbie hexpr (maybeHead bintypes) (maybeHead montypes) t exprs
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
        go e@(App (App (App (App (Var v) (Type _)) dict) a1) a2) bins mons exprs
            = if var2str v `elem` binOpList
                then let (a1',bins1,mons1,exprs1) = go a1 [] [] []
                         (a2',bins2,mons2,exprs2) = go a2 [] [] []
                         t = varType v
                     in ( EBinOp v t dict a1' a2'
                        , t:bins++bins1++bins2
                        , mons++mons1++mons2
                        , (var2str v,dict):exprs++exprs1++exprs2
                        )
                else (ELeaf e,bins,mons,[(expr2str dflags e,e)])

        -- polymorphic literals created via fromInteger/fromRational
        go e@(App (App (App (Var v) (Type _)) dict) (Lit l)) bins mons exprs
            = (ELit $ lit2rational l,bins,mons,exprs)

        -- non-polymorphic literals
        go e@(App (Var _) (Lit l)) bins mons exprs
            = (ELit $ lit2rational l,bins,mons,exprs)

        -- all unary operators have this form
        go e@(App (App (App (Var v) (Type _)) dict) a) bins mons exprs

            = {-if var2str v=="fromInteger" || var2str v=="fromRational"

                -- literals constructed from unary operations
                then error "from*"

                -- normal unary operations
                else -}if var2str v `elem` monOpList
                    then let (a',bins',mons',exprs') = go a [] [] []
                             t = varType v
                         in ( EMonOp v t dict a'
                            , bins++bins'
                            , t:mons++mons'
                            , (var2str v, dict):exprs++exprs'
                            )
                    else (ELeaf e,bins,mons,exprs)

        -- everything else
        go e bins mons exprs = (ELeaf e,bins,mons,[(expr2str dflags e,e)])

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

                dictType = mkAppTy classType (getParam $ numType herbie)
                dictVar = mkGlobalVar
                    VanillaId
                    (mkSystemName (mkUnique 'z' 76128) (mkVarOcc "herbie_magicvar"))
                    dictType
                    vanillaIdInfo

--             liftIO $ do
-- --                 putStrLn $ "eps_PTE="++showSDoc dflags (ppr $ eps_PTE eps)
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
--                 liftIO $ do
--                     putStrLn $ "nonC="++showSDoc dflags (ppr nonC)
--                     putStrLn $ "wCs="++showSDoc dflags (ppr wCs)
                (x, evBinds) <- solveWantedsTcM wCs
--                 evBinds <- simplifyTop wCs
                bnds <- initDsTc $ dsEvBinds evBinds
--                 liftIO $ do
--                     putStrLn $ "nonC="++showSDoc dflags (ppr nonC)
--                     putStrLn $ "wCs="++showSDoc dflags (ppr wCs)
--                     putStrLn $ "evBinds="++showSDoc dflags (ppr bnds)
--                     putStrLn $ "bnds="++showSDoc dflags (ppr bnds)
--                     putStrLn $ "x="++showSDoc dflags (ppr x)
                return bnds
--             bnds <- runTcM guts . initDsTc $ dsEvBinds xs
            case bnds of
                [NonRec _ dict] -> return $ dict
                [] -> --error "no bnds"
                    {-case findExpr herbie opstr of
                        Just (Var v) -> v
                        Nothing -> -}
                        do
                            let (f,ParentIs p) =  lookupNameParent opstr
                                c = head $ filter
                                    (\x -> getOccName x == nameOccName p)
                                    (concatMap getSuperClasses $ getClasses $ numType herbie)
--                                 dict =
--                             putMsgS $ "classes="++showSDoc dflags (ppr $ getClasses $ numType herbie)
--                             putMsgS $ "selids="++showSDoc dflags (ppr $ map classSCTheta $ getClasses $ numType herbie)
--                             putMsgS $ "superclasses="++showSDoc dflags (ppr $ map getSuperClasses $ getClasses $ numType herbie)
--                             putMsgS $ "f="++showSDoc dflags (ppr $ f)
--                             putMsgS $ "p="++showSDoc dflags (ppr $ p)
--                             putMsgS $ "c="++showSDoc dflags (ppr $ c)
--                             putMsgS $ "dicts="++showSDoc dflags (ppr $ getDicts $ numType herbie)
                            ret <- dictFromParamType c $ numType herbie
                            case ret of
                                Just x -> return x
--                             error $ "findExpr Nothing: "++showSDoc dflags (ppr $ p)

        ----------------------------------------
        -- recursion loop

        go (SLeaf str) = case readMaybe str :: Maybe Double of
            Just d  -> return $ ELit $ toRational d
            Nothing -> do
                dflags <- getDynFlags
                return $ ELeaf $ case findExpr herbie str of
                    Just x -> x
                    Nothing -> error $ "herbieStr2herbieExpr: var " ++ str ++ " not in scope"

        go (SOp [SLeaf opstr, a1, a2]) = do
            a1' <- go a1
            a2' <- go a2
            var <- getVar opstr
            dict <- getDict opstr
            return $ EBinOp var (getParam $ numType herbie) dict a1' a2'

        go (SOp [SLeaf opstr, a]) = do
            a' <- go a
            var <- getVar opstr
            dict <- getDict opstr
            return $ EMonOp var (getParam $ numType herbie) dict a'

        go xs = error $ "herbieStr2herbieExpr: expr arity not supported: "++show xs

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
myshow dflags = go 1
    where
        go i (Var v) = "Var "++showSDoc dflags (ppr v)++"::"++showSDoc dflags (ppr $ varType v)
        go i (Lit l) = "Lit"
        go i (Type t) = "Type "++showSDoc dflags (ppr t)
        go i (Coercion l) = "Coercion"
        go i (Lam a b) = "Lam (" ++ show a ++ ") ("++go (i+1) b++")"
        go i (Let a b) = "Let (" ++ show a ++ ") ("++go (i+1) b++")"
        go i (Cast a b) = "Case (" ++ go (i+1) a ++ ") ("++show b++")"
        go i (Tick a b) = "Tick (" ++ show a ++ ") ("++go (i+1) b++")"
        go i (Case a b c d) = "Case ("++go (i+1) a++") ("++show b++") ("++show c++") (LISTOFJUNK)"
        go i (App a b) = "App\n"++white++"(" ++ go (i+1) a ++ ")\n"++white++"("++go (i+1) b++")\n"++drop 4 white
            where
                white=replicate (4*i) ' '

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
--     show v = "name"


