{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

module Herbie.ForeignInterface
    where

import Control.Applicative
import Control.Exception
import Control.DeepSeq
import Data.List
import Data.String
import qualified Data.Text as T
import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow
import Database.SQLite.Simple.FromField
import Database.SQLite.Simple.ToField
import GHC.Generics hiding (modName)
import System.Directory
import System.Process
import System.Timeout

import Paths_HerbiePlugin
import Herbie.MathInfo
import Herbie.MathExpr

import Prelude

-- | Stores the flags that will get passed to the Herbie executable
newtype HerbieOptions = HerbieOptions [[String]]
    deriving (Show,Generic,NFData)

opts2string :: HerbieOptions -> String
opts2string (HerbieOptions opts) = concat $ intersperse " " $ concat opts

string2opts :: String -> HerbieOptions
string2opts xs = HerbieOptions [words xs]

toggleNumerics :: HerbieOptions -> HerbieOptions
toggleNumerics (HerbieOptions xs) = HerbieOptions $ go xs []
    where
        go :: [[String]] -> [[String]] -> [[String]]
        go []                           ys = ys ++ [["-o", "rules:numerics" ]]
        go (["-o","rules:numerics"]:xs) ys = ys ++ xs
        go (x:xs)                       ys = go xs (x:ys)

toggleRegimes :: HerbieOptions -> HerbieOptions
toggleRegimes (HerbieOptions xs) = HerbieOptions $ go xs []
    where
        go :: [[String]] -> [[String]] -> [[String]]
        go []                           ys = ys ++ [["-o", "reduce:regimes" ]]
        go (["-o","reduce:regimes"]:xs) ys = ys ++ xs
        go (x:xs)                       ys = go xs (x:ys)

-- | This information gets stored in a separate db table for debugging purposes
data DbgInfo = DbgInfo
    { dbgComments   :: String
    , modName       :: String
    , functionName  :: String
    , functionType  :: String
    }

-- | The result of running Herbie
data HerbieResult a = HerbieResult
    { cmdin  :: !a
    , cmdout :: !a
    , opts   :: !HerbieOptions
    , errin  :: !Double
    , errout :: !Double
    }
    deriving (Show,Generic,NFData)

instance FromField a => FromRow (HerbieResult a) where
    fromRow = HerbieResult <$> field <*> field <*> (fmap string2opts field) <*> field <*> field

instance ToField a => ToRow (HerbieResult a) where
    toRow (HerbieResult cmdin cmdout opts errin errout) = toRow
        ( cmdin
        , cmdout
        , opts2string opts
        , errin
        , errout
        )

-- | Given a MathExpr, return a numerically stable version.
stabilizeMathExpr :: DbgInfo -> HerbieOptions -> MathExpr -> IO (HerbieResult MathExpr)
stabilizeMathExpr dbgInfo opts cmdin = do
    let (cmdinLisp,varmap) = getCanonicalLispCmd $ haskellOpsToHerbieOps cmdin
    res <- stabilizeLisp dbgInfo opts cmdinLisp
    cmdout' <- do
        -- FIXME:
        -- Due to a bug in Herbie, fromCanonicalLispCmd sometimes throws an exception.
        ret <- try $ do
            let ret = herbieOpsToHaskellOps $ fromCanonicalLispCmd (cmdout res,varmap)
            deepseq ret $ return ret
        case ret of
            Left (SomeException e) -> do
                putStrLn $ "WARNING in stabilizeMathExpr: "++show e
                return cmdin
            Right x -> return x
    let res' = res
            { cmdin  = cmdin
            , cmdout = cmdout'
            }
--     putStrLn $ "  cmdin:   "++cmdinLisp
--     putStrLn $ "  cmdout:  "++cmdout res
--     putStrLn $ "  stabilizeLisp': "++mathExpr2lisp (fromCanonicalLispCmd (cmdout res,varmap))
    return res'

-- | Given a Lisp command, return a numerically stable version.
-- It first checks if the command is in the global database;
-- if it's not, then it runs "execHerbie".
stabilizeLisp :: DbgInfo -> HerbieOptions -> String -> IO (HerbieResult String)
stabilizeLisp dbgInfo opts cmd = do
    dbResult <- lookupDatabase opts cmd
    ret <- case dbResult of
        Just x -> do
            return x
        Nothing -> do
            putStrLn "  Not found in database.  Running Herbie..."
            res <- execHerbie opts cmd
            insertDatabase res
            return res
    insertDatabaseDbgInfo dbgInfo ret

    -- FIXME:
    -- Herbie has a bug where it sometimes outputs a less numerically stable version.
    -- So we need to check to make sure we return the more stable output.
    return $ if errin ret > errout ret
        then ret
        else ret { errout = errin ret, cmdout = cmdin ret }

-- | Run the `herbie` command and return the result
execHerbie :: HerbieOptions -> String -> IO (HerbieResult String)
execHerbie (HerbieOptions opts) lisp = do

    -- build the command string we will pass to Herbie
    let varstr = "("++unwords (lisp2vars lisp)++")"
        stdin = "(herbie-test "++varstr++" \"cmd\" "++lisp++") \n"

    -- Herbie can take a long time to run.
    -- Here we limit it to 2 minutes.
    --
    -- FIXME:
    -- This should be a parameter the user can pass to the plugin
    ret <- timeout 120000000 $ do

        -- launch Herbie with a fixed seed to ensure reproducible builds
        (_,stdout,stderr) <- readProcessWithExitCode
            "herbie-exec"
            (concat opts)
            stdin

        -- try to parse Herbie's output;
        -- if we can't parse it, that means Herbie had an error and we should abort gracefully
        ret <- try $ do
            let (line1:line2:line3:_) = lines stdout
            let ret = HerbieResult
                    { errin
                        = read
                        $ drop 1
                        $ dropWhile (/=':') line1
                    , errout
                        = read
                        $ drop 1
                        $ dropWhile (/=':') line2
                    , opts
                        = HerbieOptions opts
                    , cmdin
                        = lisp
                    , cmdout
                        = (!!2)
                        $ groupByParens
                        $ init
                        $ tail line3
                    }
            deepseq ret $ return ret

        case ret of
            Left (SomeException e) -> do
                putStrLn $ "WARNING in execHerbie: "++show e
                putStrLn $ "WARNING in execHerbie: stdin="++stdin
                putStrLn $ "WARNING in execHerbie: stdout="++stdout
                return HerbieResult
                    { errin  = 0/0
                    , errout = 0/0
                    , opts   = HerbieOptions opts
                    , cmdin  = lisp
                    , cmdout = lisp
                    }
            Right x -> return x

    case ret of
        Just x -> return x
        Nothing -> do
            putStrLn $ "WARNING: Call to Herbie timed out after 2 minutes."
            return $ HerbieResult
                { errin  = 0/0
                , errout = 0/0
                , opts   = HerbieOptions opts
                , cmdin  = lisp
                , cmdout = lisp
                }


-- | Returns a connection to the sqlite3 database
mkConn = do
    path <- getDataFileName "Herbie.db"
    open path

-- | Check the database to see if we already know the answer for running Herbie
--
-- FIXME:
-- When Herbie times out, NULL gets inserted into the database for errin and errout.
-- The Sqlite3 bindings don't support putting NULL into Double's as NaNs,
-- so the query below raises an exception.
-- This isn't so bad, except a nasty error message gets printed,
-- and the plugin attempts to run Herbie again (wasting a lot of time).
lookupDatabase :: HerbieOptions -> String -> IO (Maybe (HerbieResult String))
lookupDatabase opts cmdin = do
    ret <- try $ do
        conn <- mkConn
        res <- queryNamed
            conn
            "SELECT cmdin,cmdout,opts,errin,errout from HerbieResults where cmdin = :cmdin and opts = :opts"
            [":cmdin" := cmdin, ":opts" := opts2string opts]
            :: IO [HerbieResult String]
        close conn
        return $ case res of
            [x] -> Just x
            []  -> Nothing
    case ret of
        Left (SomeException e) -> do
            putStrLn $ "WARNING in lookupDatabase: "++show e
            return Nothing
        Right x -> return x

-- | Inserts a "HerbieResult" into the global database of commands
insertDatabase :: HerbieResult String -> IO ()
insertDatabase res = do
    ret <- try $ do
        conn <- mkConn
        execute_ conn $ fromString $
            "CREATE TABLE IF NOT EXISTS HerbieResults "
            ++"( id INTEGER PRIMARY KEY"
            ++", cmdin  TEXT        NOT NULL"
            ++", cmdout TEXT        NOT NULL"
            ++", opts   TEXT        NOT NULL"
            ++", errin  DOUBLE      "
            ++", errout DOUBLE      "
            ++", UNIQUE (cmdin, opts)"
            ++")"
        execute_ conn "CREATE INDEX IF NOT EXISTS HerbieResultsIndex ON HerbieResults(cmdin)"
        execute conn "INSERT INTO HerbieResults (cmdin,cmdout,opts,errin,errout) VALUES (?,?,?,?,?)" res
        close conn
    case ret of
        Left (SomeException e) -> putStrLn $ "WARNING in insertDatabase: "++show e
        Right _ -> return ()
    return ()

insertDatabaseDbgInfo :: DbgInfo -> HerbieResult String -> IO ()
insertDatabaseDbgInfo dbgInfo res = do
    ret <- try $ do
        conn <- mkConn
        execute_ conn $ fromString $
            "CREATE TABLE IF NOT EXISTS DbgInfo "
            ++"( id INTEGER PRIMARY KEY"
            ++", resid INTEGER NOT NULL"
            ++", dbgComments TEXT"
            ++", modName TEXT"
            ++", functionName TEXT"
            ++", functionType TEXT"
            ++")"
        res <- queryNamed
            conn
            "SELECT id,cmdout from HerbieResults where cmdin = :cmdin"
            [":cmdin" := cmdin res]
            :: IO [(Int,String)]
        execute conn "INSERT INTO DbgInfo (resid,dbgComments,modName,functionName,functionType) VALUES (?,?,?,?,?)" (fst $ head res,dbgComments dbgInfo,modName dbgInfo,functionName dbgInfo,functionType dbgInfo)
        close conn
    case ret of
        Left (SomeException e) -> putStrLn $ "WARNING in insertDatabaseDbgInfo: "++show e
        Right _ -> return ()
    return ()
