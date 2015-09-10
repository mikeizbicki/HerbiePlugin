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

import Data.Maybe

import Debug.Trace

import Stabalize.Herbie
import Stabalize.MathExpr
import Stabalize.MathInfo

import Prelude
import Show
import Data.IORef

plugin :: Plugin
plugin = defaultPlugin
    { installCoreToDos = install
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todo = do
    reinitializeGlobals
    return (CoreDoPluginPass "MathInfo" pass : todo)

pass :: ModGuts -> CoreM ModGuts
pass guts = do
    dflags <- getDynFlags
    liftIO $ writeIORef dynFlags_ref dflags
    bindsOnlyPass (mapM (modBind guts)) guts

-- | This function gets run on each binding on the Haskell source file.
modBind :: ModGuts -> CoreBind -> CoreM CoreBind
modBind guts bndr@(Rec _) = return bndr
modBind guts bndr@(NonRec b e) = do
    dflags <- getDynFlags
    putMsgS ""
    putMsgS $ showSDoc dflags (ppr b)
        ++ "::"
        ++ showSDoc dflags (ppr $ varType b)
    putMsgS $ myshow dflags e
    return bndr
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

                    -- Non-recursive let binding:
                    -- If the variable is a dictionary, add it to the list;
                    -- Always recurse into the subexpression
                    Let bndr@(NonRec a e) b -> do
                        let a' = undeadenId a
                        b' <- go (extractDicts a'++dicts) b
                        return $ Let (NonRec a' e) b'

                    -- Function application:
                    -- Math expressions may appear on either side, so recurse on both
                    App a b -> do
                        a' <- go dicts a
                        b' <- go dicts b
                        return $ App a' b'

                    -- FIXME: needs to be exhaustive
                    otherwise -> do
--                         putMsgS $ "  not mathexpr: " ++ showSDoc dflags (ppr e)
                        return e

                -- we found a math expression, so process it
                Just mathInfo -> do
                    putMsgS $ "Found math expression within binding "
                        ++ showSDoc dflags (ppr b)
                        ++ "::"
                        ++ showSDoc dflags (ppr $ varType b)
                    putMsgS $ "  type   = "++showSDoc dflags (ppr $ getParam $ numType mathInfo)
                    putMsgS $ "  before = "++herbie2lisp dflags mathInfo
--                     putMsgS $ "  before (core): "++showSDoc dflags (ppr e)

--                     putMsgS $ "    expression "++herbie2lisp dflags herbie
--                     putMsgS $ "  before (lisp): "++herbie2lisp dflags herbie
--                     putMsgS $ ""
--                     putMsgS $ "  before (core): "++showSDoc dflags (ppr e)
                    putMsgS $ ""
                    putMsgS $ "  before (raw ): "++myshow dflags e
--                     putMsgS $ "  before (raw ): "++show e
--                     putMsgS $ ""
--                     StabilizerResult _ e' _ _ <- callHerbie guts e mathInfo
--                     e' <- stabilizeMathInfo guts mathInfo
                    res <- liftIO $ stabilizeMathExpr $ hexpr mathInfo
                    let mathInfo' = mathInfo { hexpr = cmdout res }
                    e' <- mathInfo2expr guts mathInfo'
                    putMsgS $ "           "++show (errin res)++" bits of error"
                    putMsgS $ "  after  = "++herbie2lisp dflags mathInfo'
                    putMsgS $ "           "++show (errout res)++" bits of error"
--                     putMsgS $ "  after  (core): "++showSDoc dflags (ppr e')
                    putMsgS $ ""
                    putMsgS $ "  after  (raw ): "++myshow dflags e'
--                     putMsgS $ "  after  (raw ): "++show e'
--                     putMsgS $ ""
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
