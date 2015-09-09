{-# LANGUAGE OverloadedStrings,ScopedTypeVariables,DeriveGeneric,DeriveAnyClass #-}

module Stabalize.Herbie
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
import GHC.Generics
import System.Directory
import System.Process

import Stabalize.MathInfo
import Stabalize.MathExpr

-- | The result of running Herbie
data StabilizerResult a = StabilizerResult
    { cmdin  :: !a
    , cmdout :: !a
    , errin  :: !Double
    , errout :: !Double
    }
    deriving (Show,Generic,NFData)

instance FromField a => FromRow (StabilizerResult a) where
    fromRow = StabilizerResult <$> field <*> field <*> field <*> field

instance ToField a => ToRow (StabilizerResult a) where
    toRow (StabilizerResult cmdin cmdout errin errout) = toRow (cmdin, cmdout, errin, errout)

-- | Given a MathExpr, return a numerically stable version.
stabilizeMathExpr :: MathExpr -> IO (StabilizerResult MathExpr)
stabilizeMathExpr cmdin = do
    let (cmdinLisp,varmap) = getCanonicalLispCmd cmdin
    res <- stabilizeLisp cmdinLisp
--     putStrLn $ "stabilizeLisp:  "++cmdout res
--     putStrLn $ "stabilizeLisp': "++mathExpr2lisp (fromCanonicalLispCmd (cmdout res,varmap))
    return $ res
        { cmdin  = cmdin
        , cmdout = fromCanonicalLispCmd (cmdout res,varmap)
        }

-- | Given a Lisp command, return a numerically stable version.
-- It first checks if the command is in the global database;
-- if it's not, then it runs "execHerbie".
stabilizeLisp :: String -> IO (StabilizerResult String)
stabilizeLisp cmdin = do
    dbResult <- lookupDatabase cmdin
    ret <- case dbResult of
        Just x -> do
--             putStrLn "    Found in database."
            return x
        Nothing -> do
--             putStrLn "    Not found in database.  Running Herbie..."
            res <- execHerbie cmdin
            insertDatabase res
            return res
    if not $ "(if " `isInfixOf` cmdout ret
        then return ret
        else do
            putStrLn "WARNING: Herbie's output contains if statements, which aren't yet supported"
            putStrLn "WARNING: Using original numerically unstable equation."
            return $ ret
                { errout = errin ret
                , cmdout = cmdin
                }
--     return $ ret { cmdout = "(+ herbie0 herbie1)" }

-- | Run the `herbie` command and return the result
execHerbie :: String -> IO (StabilizerResult String)
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
        stdin = "(herbie-test "++varstr++" \"cmd\" "++lisp++") \n"

    ret <- try $ do
        (_,stdout,stderr) <- readProcessWithExitCode
            "herbie-exec"
            [ "-r", "#(1461197085 2376054483 1553562171 1611329376 2497620867 2308122621)" ]
            stdin
        let (line2:line3:line4:_) = lines stdout
        let ret = StabilizerResult
                { errin
                    = read
                    $ drop 1
                    $ dropWhile (/=':')
                    $ line2
                , errout
                    = read
                    $ drop 1
                    $ dropWhile (/=':')
                    $ line3
                , cmdin
                    = lisp
                , cmdout
                    = init
                    $ dropWhile (/='(')
                    $ drop 1
                    $ dropWhile (/='(')
                    $ drop 1
                    $ dropWhile (/='(')
                    $ take (length stdout-2)
                    $ line4
                }
        deepseq ret $ return ret

    case ret of
        Left (SomeException e) -> do
            putStrLn $ "WARNING in execHerbie: "++show e
            return $ StabilizerResult
                { errin  = 0/0
                , errout = 0/0
                , cmdin  = lisp
                , cmdout = lisp
                }
        Right x -> return x

    where
        -- We just need to add spaces around the parens before calling "words"
        tokenize :: String -> [String]
        tokenize = words . concat . map go
            where
                go '(' = " ( "
                go ')' = " ) "
                go x   = [x]

-- | Check the database to see if we already know the answer for running Herbie
lookupDatabase :: String -> IO (Maybe (StabilizerResult String))
lookupDatabase cmdin = do
    ret <- try $ do
        dirname <- getAppUserDataDirectory "Stabalizer"
        createDirectoryIfMissing True dirname
        conn <- open $ dirname++"/Stabalizer.db"
        res <- queryNamed
            conn
            "SELECT cmdin,cmdout,errin,errout from StabilizerResults where cmdin = :cmdin"
            [":cmdin" := cmdin]
            :: IO [StabilizerResult String]
        close conn
        return $ case res of
            [x] -> Just x
            []  -> Nothing
    case ret of
        Left (SomeException e) -> do
            putStrLn $ "WARNING in lookupDatabase: "++show e
            return Nothing
        Right x -> return x

-- | Inserts a "StabilizerResult" into the global database of commands
insertDatabase :: StabilizerResult String -> IO ()
insertDatabase res = do
    ret <- try $ do
        dirname <- getAppUserDataDirectory "Stabalizer"
        createDirectoryIfMissing True dirname
        conn <- open $ dirname++"/Stabalizer.db"
        execute_ conn $ fromString $
            "CREATE TABLE IF NOT EXISTS StabilizerResults "
            ++"( id INTEGER PRIMARY KEY"
            ++", cmdin  TEXT UNIQUE NOT NULL"
            ++", cmdout TEXT        NOT NULL"
            ++", errin  DOUBLE      NOT NULL"
            ++", errout DOUBLE      NOT NULL"
            ++")"
        execute_ conn "CREATE INDEX IF NOT EXISTS StabilizerResultsIndex ON StabilizerResults(cmdin)"
        execute conn "INSERT INTO StabilizerResults (cmdin,cmdout,errin,errout) VALUES (?,?,?,?)" res
        close conn
    case ret of
        Left (SomeException e) -> putStrLn $ "WARNING in insertDatabase: "++show e
        Right _ -> return ()
    return ()
