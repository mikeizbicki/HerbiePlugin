module Herbie
    ( plugin
    )
    where

import Class
import DsBinds
import DsMonad
import ErrUtils
import GhcPlugins
import Id
import Unique
import MkId
import PrelNames
import TcRnMonad
import TcSimplify

import Control.Monad
import Control.Monad.Except
import Data.Maybe

import Herbie.CoreManip
import Herbie.ForeignInterface
import Herbie.MathExpr
import Herbie.MathInfo

import Debug.Trace

import Prelude
import Show
import Data.IORef

plugin :: Plugin
plugin = defaultPlugin
    { installCoreToDos = install
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todo = do
    putMsgS "Compiling with Herbie floating point stabilization"
    reinitializeGlobals
    return (CoreDoPluginPass "MathInfo" (pass opts) : todo)

pass :: [CommandLineOption] -> ModGuts -> CoreM ModGuts
pass opts guts = do
    dflags <- getDynFlags
    liftIO $ writeIORef dynFlags_ref dflags
    bindsOnlyPass (mapM (modBind opts guts)) guts

-- | This function gets run on each binding on the Haskell source file.
modBind :: [CommandLineOption] -> ModGuts -> CoreBind -> CoreM CoreBind
modBind opts guts bndr@(Rec _) = return bndr
modBind opts guts bndr@(NonRec b e) = do
--     dflags <- getDynFlags
--     putMsgS ""
--     putMsgS $ showSDoc dflags (ppr b)
--         ++ "::"
--         ++ showSDoc dflags (ppr $ varType b)
--     putMsgS $ myshow dflags e
--     return bndr
    e' <- go [] e
    return $ NonRec b e'
    where
        -- Recursively descend into the expression e.
        -- For each math expression we find, run Herbie on it.
        -- We need to save each dictionary we find because
        -- it might be needed to create the replacement expressions.
        go dicts e = do
            dflags <- getDynFlags
            case mkMathInfo dflags dicts (varType b) e of

                -- not a math expression, so recurse into subexpressions
                Nothing -> case e of

                    -- Lambda expression:
                    -- If the variable is a dictionary, add it to the list;
                    -- Always recurse into the subexpression
                    --
                    -- FIXME:
                    -- Currently, we're removing deadness annotations from any dead variables.
                    -- This is so that we can use all the dictionaries that the type signatures allow.
                    -- Core lint complains about using dead variables if we don't.
                    -- This causes us to remove ALL deadness annotations in the entire program.
                    -- I'm not sure the drawback of this.
                    -- This could be fixed by having a second pass through the code
                    -- to remove only the appropriate deadness annotations.
                    Lam a b -> do
                        let a' = undeadenId a
                        b' <- go (extractDicts a'++dicts) b
                        return $ Lam a' b'

                    -- Let binding:
                    -- If the variable is a dictionary, add it to the list;
                    -- Always recurse into the subexpression
                    Let (NonRec a e) b -> do
                        let a' = undeadenId a
                        e' <- go dicts e
                        b' <- go (extractDicts a'++dicts) b
                        return $ Let (NonRec a' e') b'

                    Let (Rec bndrs) expr -> do
                        bndrs' <- forM bndrs $ \(a,e) -> do
                            let a' = undeadenId a
                            e' <- go dicts e
                            return (a',e')
                        expr' <- go dicts expr
                        return $ Let (Rec bndrs') expr'

                    -- Function application:
                    -- Math expressions may appear on either side, so recurse on both
                    App a b -> do
                        a' <- go dicts a
                        b' <- go dicts b
                        return $ App a' b'

                    -- Case statement:
                    -- Math expressions may appear in the condition or in any of the branches
                    Case cond w t es -> do
                        cond' <- go dicts cond
                        es' <- forM es $ \ (altcon, xs, expr) -> do
                            expr' <- go dicts expr
                            return $ (altcon, xs, expr')
                        return $ Case cond' w t es'

                    -- Ticks and Casts are just annotating extra information on an expression.
                    -- We ignore the extra information and recurse into the expression.
                    Tick a b -> do
                        b' <- go dicts b
                        return $ Tick a b'

                    Cast a b -> do
                        a' <- go dicts a
                        return $ Cast a' b

                    -- There's nothing to do for these statements.
                    -- They form the recursion's base case.
                    Var v      -> return $ Var v
                    Lit l      -> return $ Lit l
                    Type t     -> return $ Type t
                    Coercion c -> return $ Coercion c

                -- We found a math expression, so process it
                Just mathInfo -> do
                    putMsgS $ "Found math expression within binding "
                        ++ showSDoc dflags (ppr b)
                        ++ " :: "
                        ++ showSDoc dflags (ppr $ varType b)
                    putMsgS $ "  original expression = "++pprMathInfo mathInfo
                    let dbgInfo = DbgInfo
                            { dbgComments  = concat opts
                            , modName      = showSDoc dflags (ppr $ moduleName $ mg_module guts)
                            , functionName = showSDoc dflags (ppr b)
                            , functionType = showSDoc dflags (ppr $ varType b)
                            }
                    res <- liftIO $ stabilizeMathExpr dbgInfo $ hexpr mathInfo
                    let mathInfo' = mathInfo { hexpr = cmdout res }
                    putMsgS $ "  improved expression = "++pprMathInfo mathInfo'
                    putMsgS $ "  original error = "++show (errin res)++" bits"
                    putMsgS $ "  improved error = "++show (errout res)++" bits"
                    ret <- runExceptT $ mathInfo2expr guts mathInfo'
                    case ret of
                        Left str -> do
                            putMsgS "  WARNING: Not substituting the improved expression into your code"
                            putMsgS str
                            return e
                        Right e' -> do
--                             putMsgS $ "  before = " ++ myshow dflags e
--                             putMsgS $ "  after = " ++ myshow dflags e'
                            return e'

-- | Return a list with the given variable if the variable is a dictionary or tuple of dictionaries,
-- otherwise return [].
extractDicts :: Var -> [Var]
extractDicts v = case classifyPredType (varType v) of
    ClassPred _ _ -> [v]
    EqPred _ _ _  -> [v]
    TuplePred _   -> [v]
    IrredPred _   -> []

-- | If a variable is marked as dead, remove the marking
undeadenId :: Var -> Var
undeadenId a = if isDeadBinder a
    then setIdOccInfo a NoOccInfo
    else a
