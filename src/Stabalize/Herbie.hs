{-# LANGUAGE OverloadedStrings,ScopedTypeVariables #-}

module Stabalize.Herbie
    where

import GhcPlugins

import Control.Exception
import Control.Applicative
import qualified Data.Text as T
import Data.List
import Data.String
import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow
import System.Directory
import System.Process

import Stabalize.MathInfo
import Stabalize.MathExpr

--------------------------------------------------------------------------------
-- Herbie interface

callHerbie :: ModGuts -> Expr Var -> MathInfo -> CoreM (Expr CoreBndr)
callHerbie guts expr herbie = do
    let (lispstr,varmap) = getCanonicalLispCmd $ hexpr herbie
    dbResult <- liftIO $ lookupDatabase lispstr
    lispstr' <- case dbResult of
        Just x -> do
            putMsgS "    Found in database."
            return x
        Nothing -> do
            putMsgS "    Not found in database.  Running Herbie..."
            liftIO $ do
                res <- execHerbie lispstr
                insertDatabase lispstr res
                return res
    let herbie' = herbie { hexpr = fromCanonicalLispCmd (lispstr',varmap) }
    mathInfo2expr guts herbie'

execHerbie :: String -> IO String
execHerbie lisp = do
    let vars = nub
             $ sort
             $ filter (\x -> x/="("
                          && x/=")"
                          && not (x `elem` binOpList)
                          && not (x `elem` monOpList)
                          && not (head x `elem` ("1234567890"::String))
                      ) $ tokenize lisp :: [String]
        varstr = "("++(intercalate " " vars)++")"
        cmd = "(herbie-test "++varstr++" \"cmd\" "++lisp++") \n"
    (_,stdout,stderr) <- readProcessWithExitCode "herbie-exec" [] cmd
    let lisp' = dropWhile (/='(')
              $ drop 1
              $ dropWhile (/='(')
              $ drop 1
              $ dropWhile (/='(')
              $ take (length stdout-2)
              $ stdout
    return lisp'

-- | We just need to add spaces around the parens before calling "words"
tokenize :: String -> [String]
tokenize = words . concat . map go
    where
        go '(' = " ( "
        go ')' = " ) "
        go x   = [x]

----------------------------------------

lookupDatabase :: String -> IO (Maybe String)
lookupDatabase str = do
    ret <- try $ do
        dirname <- getAppUserDataDirectory "Stabalizer"
        createDirectoryIfMissing True dirname
        conn <- open $ dirname++"/Stabalizer.db"
        res <- queryNamed
            conn
            "SELECT id,stabilized from StabilizedMap where original = :original"
            [":original" := str]
            :: IO [(Int,String)]
        close conn
        return $ case res of
            [x] -> Just $ snd x
            []  -> Nothing
    case ret of
        Left (SomeException e) -> do
            putStrLn $ "WARNING in lookupDatabase: "++show e
            return Nothing
        Right x -> return $ x

insertDatabase :: String -> String -> IO ()
insertDatabase orig simpl = do
    ret <- try $ do
        dirname <- getAppUserDataDirectory "Stabalizer"
        createDirectoryIfMissing True dirname
        conn <- open $ dirname++"/Stabalizer.db"
        execute_ conn "CREATE TABLE IF NOT EXISTS StabilizedMap (id INTEGER PRIMARY KEY, original TEXT UNIQUE NOT NULL, stabilized TEXT NOT NULL)"
        execute_ conn "CREATE INDEX IF NOT EXISTS StabilizedMapIndex ON StabilizedMap(original)"
        execute conn "INSERT INTO StabilizedMap (original,stabilized) VALUES (?,?)" (orig,simpl)
        close conn
    case ret of
        Left (SomeException e) -> putStrLn $ "WARNING in insertDatabase: "++show e
        Right _ -> return ()
    return ()
