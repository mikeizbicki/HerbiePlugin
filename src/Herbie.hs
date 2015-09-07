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
import PrelNames
import TcRnMonad
import TcSimplify

import Language.Haskell.TH (mkName)
import Data.Char
import Data.List
import Data.Maybe
import System.Process

import Debug.Trace

import Stabalize.MathExpr

import Prelude
ifThenElse True t f = t
ifThenElse False t f = f


--------------------------------------------------------------------------------
-- GHC plugin interface

plugin :: Plugin
plugin = defaultPlugin
    { installCoreToDos = install
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
    reinitializeGlobals
    return (CoreDoPluginPass "MathInfo" pass : todo)

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
                        ELeaf _ -> case e of
                            Lam a b -> do
                                let dicts' = if (head $ occNameString $ nameOccName $ varName a)=='$'
                                        then a:dicts
                                        else dicts
                                b' <- go dicts' b
                                return $ Lam a b'
                            Let a b -> do
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
                            putMsgS $ "  before (raw ): "++myshow dflags e
--                             putMsgS $ "  before (raw ): "++show e
                            putMsgS $ ""
                            e' <- callHerbie guts e herbie
                            let herbie' = expr2herbie dflags paramtype e'
                            putMsgS $ "  after  (lisp): "++herbie2lisp dflags herbie'
                            putMsgS $ ""
--                             putMsgS $ "  after  (core): "++showSDoc dflags (ppr e')
--                             putMsgS $ ""
                            putMsgS $ "  after  (raw ): "++myshow dflags e'
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

-- | Given a list of member functions of a class,
-- return the function that extracts the dictionary corresponding to c.
findSelId :: Class -> [Var] -> Var
findSelId c [] = error "findSelId: this shouldn't happen"
findSelId c (v:vs) = if isDictSelector c v
    then v
    else findSelId c vs

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

expr2str :: DynFlags -> Expr Var -> String
expr2str dflags (Var v) = {-"var_" ++-} var2str v
expr2str dflags e       = "expr_" ++ (decorate $ showSDoc dflags (ppr e))
    where
        decorate :: String -> String
        decorate = map go
            where
                go x = if not (isAlphaNum x) --x `elem` " @$()%':\"{}[]\n\t"
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

mathExpr2expr :: ModGuts -> MathInfo -> CoreM (Expr CoreBndr)
mathExpr2expr guts herbie = go (hexpr herbie)
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

        -- leaf is a numeric literal
        go (ELit r) = do
            from <- getVar guts "fromRational"
            fromDict <- getDict "fromRational"
            -- FIXME: the type of the "to" variable is wrong (it's too polymorphic),
            -- but I'm not sure the best way to fix it and GHC doesn't seem to care.
            to <- getVar guts "toRational"
            toDict <- do
                maybeDict <- getDictConcrete guts "toRational" doubleTy
                case maybeDict of
                    Just x -> return x

            return $ App
                (App
                    (App
                        (Var from )
                        (Type $ getParam $ numType herbie)
                    )
                    fromDict
                )
                (App
                    (App
                        (App
                            (Var to ) -- $ setVarType to $ mkFunTy doubleTy $ mkTyConTy $ mkFunTyCon rationalTyConName anyKind)
                            (Type doubleTy)
                        )
                        toDict
                    )
                    (mkConApp doubleDataCon [mkDoubleLit r] )
                )

        -- leaf is any other expression
        go (ELeaf str) = do
            dflags <- getDynFlags
            return $ case findExpr herbie str of
                Just x -> x
                Nothing -> error $ "mathExpr2expr: var " ++ str ++ " not in scope"
                    ++"; in scope vars="++show (map fst $ getExprs herbie)


----------------------------------------

expr2herbie :: DynFlags -> ParamType -> Expr Var -> MathInfo
expr2herbie dflags t e = MathInfo hexpr t exprs
    where
        (hexpr,exprs) = go e []

        go :: Expr Var
           -> [(String,Expr Var)]
           -> (MathExpr,[(String,Expr Var)])

        -- we need to special case the $ operator for when MathExpr is run before any rewrite rules
        go e@(App (App (App (App (Var v) (Type _)) (Type _)) a1) a2) exprs
            = if var2str v == "$"
                then go (App a1 a2) exprs
                else (ELeaf $ expr2str dflags e,[(expr2str dflags e,e)])

        -- all binary operators have this form
        go e@(App (App (App (App (Var v) (Type _)) dict) a1) a2) exprs
            = if var2str v `elem` binOpList
                then let (a1',exprs1) = go a1 []
                         (a2',exprs2) = go a2 []
                     in ( EBinOp (var2str v) a1' a2'
                        , exprs++exprs1++exprs2
                        )
                else (ELeaf $ expr2str dflags e,[(expr2str dflags e,e)])

        -- polymorphic literals created via fromInteger/fromRational
        go e@(App (App (App (Var v) (Type _)) dict) (Lit l)) exprs
            = (ELit $ lit2rational l, exprs)

        -- non-polymorphic literals
        go e@(App (Var _) (Lit l)) exprs
            = (ELit $ lit2rational l, exprs)

        -- all unary operators have this form
        go e@(App (App (App (Var v) (Type _)) dict) a) exprs
            = if var2str v `elem` monOpList
                then let (a',exprs') = go a []
                     in ( EMonOp (var2str v) a'
                        , exprs++exprs'
                        )
                else (ELeaf $ expr2str dflags e,(expr2str dflags e,e):exprs)

        -- everything else
        go e exprs = (ELeaf $ expr2str dflags e,[(expr2str dflags e,e)])

binOpList = [ "*", "/", "-", "+", "max", "min" ]
monOpList = [ "cos", "sin", "tan", "log", "sqrt" ]

----------------------------------------
-- get information from the environment

-- | Converts a String that contains a name of a variable into the compiler's internal representation of that variable.
getNameParent :: ModGuts -> String -> (Name,Parent)
getNameParent guts str = case filter isCorrectVar (concat $ occEnvElts (mg_rdr_env guts)) of
    xs -> (gre_name $ head $ xs, gre_par $ head $ xs)
    where
        isCorrectVar x = (occNameString $ nameOccName $ gre_name x) == str
                      && (case gre_par x of NoParent -> False; _ -> True)

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
getDictConcrete guts opstr t = trace "poly" $ do
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
            (mkSystemName (mkUnique 'z' 76128) (mkVarOcc "herbie_magicvar"))
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
-- Herbie interface

herbie2cmd :: DynFlags -> MathInfo -> String
herbie2cmd dflags herbie = "(herbie-test "++varStr++" \"cmd\" "++herbie2lisp dflags herbie++" )\n"
    where
        varStr = "(" ++ intercalate " " (map fst (getExprs herbie)) ++ ")"

callHerbie :: ModGuts -> Expr Var -> MathInfo -> CoreM (Expr CoreBndr)
callHerbie guts expr herbie = do
    dflags <- getDynFlags
    let lispstr = herbie2lisp dflags herbie
    lispstr' <- liftIO $ execHerbie lispstr
    putMsgS $ "lispstr'=" ++ lispstr'
    let herbie' = herbie { hexpr = str2mathExpr lispstr' }
    mathExpr2expr guts herbie'
--     let herbie' = herbie { hexpr = str2mathExpr "(+ x1 2.2)" }
--     mathExpr2expr guts herbie'

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

-- | We just need to add spaces around the parens before calling "words"
tokenize :: String -> [String]
tokenize = words . concat . map go
    where
        go '(' = " ( "
        go ')' = " ) "
        go x   = [x]

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
-- debugging

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
        go i (Lit (LitInteger l _)) = "IntegerLiteral "++show (fromIntegral l :: Double)
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
    show v = getString v


