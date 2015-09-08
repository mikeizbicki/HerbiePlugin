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

import Data.Maybe

import Debug.Trace

import Stabalize.Herbie
import Stabalize.MathExpr
import Stabalize.MathInfo

import Prelude

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
    bindsOnlyPass (mapM (modBind guts)) guts

-- | This function gets run on each binding on the Haskell source file.
modBind :: ModGuts -> CoreBind -> CoreM CoreBind
modBind guts bndr@(Rec _) = return bndr
modBind guts bndr@(NonRec b e) = do
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
                    Lam a b -> do
                        let dicts' = if (head $ occNameString $ nameOccName $ varName a)=='$'
                                then a:dicts
                                else dicts
                        b' <- go dicts' b
                        return $ Lam a b'
                    Let a b -> do
                        b' <- go dicts b
                        return $ Let a b'
                    App a b -> do
                        a' <- go dicts a
                        b' <- go dicts b
                        return $ App a' b'
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
--                     putMsgS $ ""
--                     putMsgS $ "  before (raw ): "++myshow dflags e
--                     putMsgS $ "  before (raw ): "++show e
--                     putMsgS $ ""
--                     StabilizerResult _ e' _ _ <- callHerbie guts e mathInfo
--                     e' <- stabilizeMathInfo guts mathInfo
                    res <- liftIO $ stabilizeMathExpr $ hexpr mathInfo
                    let mathInfo' = mathInfo { hexpr = cmdout res }
                    e' <- mathInfo2expr guts mathInfo'
                    let Just mathInfo' = mkMathInfo dflags dicts (varType b) e'
                    putMsgS $ "           "++show (errin res)++" bits of error"
                    putMsgS $ "  after  = "++herbie2lisp dflags mathInfo'
                    putMsgS $ "           "++show (errout res)++" bits of error"
--                     putMsgS $ "  after  (core): "++showSDoc dflags (ppr e')
--                     putMsgS $ ""
--                     putMsgS $ "  after  (raw ): "++myshow dflags e'
--                     putMsgS $ "  after  (raw ): "++show e'
--                     putMsgS $ ""
                    return e'
