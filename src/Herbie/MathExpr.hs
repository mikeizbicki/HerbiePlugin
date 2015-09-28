{-# LANGUAGE DeriveAnyClass,DeriveGeneric #-}
module Herbie.MathExpr
    where

import Control.DeepSeq
import Data.List
import Data.List.Split
import Data.Maybe
import GHC.Generics

import Debug.Trace
import Prelude
ifThenElse True t f = t
ifThenElse False t f = f

-------------------------------------------------------------------------------
-- constants that define valid math expressions

monOpList =
    [ "cos"
    , "sin"
    , "tan"
    , "acos"
    , "asin"
    , "atan"
    , "cosh"
    , "sinh"
    , "tanh"
    , "exp"
    , "log"
    , "sqrt"
    , "abs"
    , "size"
    ]

binOpList = [ "^", "**", "^^", "/", "-", "expt" ] ++ commutativeOpList
commutativeOpList = [ "*", "+"] -- , "max", "min" ]

--------------------------------------------------------------------------------

-- | Stores the AST for a math expression in a generic form that requires no knowledge of Core syntax.
data MathExpr
    = EBinOp String MathExpr MathExpr
    | EMonOp String MathExpr
    | EIf MathExpr MathExpr MathExpr
    | ELit Rational
    | ELeaf String
    deriving (Show,Eq,Generic,NFData)

instance Ord MathExpr where
    compare (ELeaf _) (ELeaf _) = EQ
    compare (ELeaf _) _         = LT

    compare (ELit r1) (ELit r2) = compare r1 r2
    compare (ELit _ ) (ELeaf _) = GT
    compare (ELit _ ) _         = LT

    compare (EMonOp op1 e1) (EMonOp op2 e2) = case compare op1 op2 of
        EQ -> compare e1 e2
        x  -> x
    compare (EMonOp _ _) (ELeaf _) = GT
    compare (EMonOp _ _) (ELit  _) = GT
    compare (EMonOp _ _) _         = LT

    compare (EBinOp op1 e1a e1b) (EBinOp op2 e2a e2b) = case compare op1 op2 of
        EQ -> case compare e1a e2a of
            EQ -> compare e1b e2b
            _  -> EQ
        _ -> EQ
    compare (EBinOp _ _ _) _ = LT

-- | Converts all Haskell operators in the MathExpr into Herbie operators
haskellOpsToHerbieOps :: MathExpr -> MathExpr
haskellOpsToHerbieOps = go
    where
        go (EBinOp op e1 e2) = EBinOp op' (go e1) (go e2)
            where
                op' = case op of
                    "**"   -> "expt"
                    "^^"   -> "expt"
                    "^"    -> "expt"
                    x      -> x

        go (EMonOp op e1) = EMonOp op' (go e1)
            where
                op' = case op of
                    "size" -> "abs"
                    x      -> x

        go (EIf cond e1 e2) = EIf (go cond) (go e1) (go e2)
        go x = x

-- | Converts all Herbie operators in the MathExpr into Haskell operators
herbieOpsToHaskellOps :: MathExpr -> MathExpr
herbieOpsToHaskellOps = go
    where
        go (EBinOp op e1 e2) = EBinOp op' (go e1) (go e2)
            where
                op' = case op of
                    "^"    -> "**"
                    "expt" -> "**"
                    x      -> x

        go (EMonOp "sqr" e1) = EBinOp "*" (go e1) (go e1)
        go (EMonOp op e1) = EMonOp op' (go e1)
            where
                op' = case op of
                    "-" -> "negate"
                    "abs" -> "size"
                    x   -> x

        go (EIf cond e1 e2) = EIf (go cond) (go e1) (go e2)
        go x = x

-- | Replace all the variables in the MathExpr with canonical names (x0,x1,x2...)
-- and reorder commutative binary operations.
-- This lets us more easily compare MathExpr's based on their structure.
-- The returned map lets us convert the canoncial MathExpr back into the original.
toCanonicalMathExpr :: MathExpr -> (MathExpr,[(String,String)])
toCanonicalMathExpr e = go [] e
    where
        go :: [(String,String)] -> MathExpr -> (MathExpr,[(String,String)])
        go acc (EBinOp op e1 e2) = (EBinOp op e1' e2',acc2')
            where
                (e1_,e2_) = if op `elem` commutativeOpList
                    then (min e1 e2,max e1 e2)
                    else (e1,e2)

                (e1',acc1') = go acc e1_
                (e2',acc2') = go acc1' e2_

        go acc (EMonOp op e1) = (EMonOp op e1', acc1')
            where
                (e1',acc1') = go acc e1
        go acc (ELit r) = (ELit r,acc)
        go acc (ELeaf str) = (ELeaf str',acc')
            where
                (acc',str') = case lookup str acc of
                    Nothing -> ((str,"herbie"++show (length acc)):acc, "herbie"++show (length acc))
                    Just x -> (acc,x)

-- | Convert a canonical MathExpr into its original form.
--
-- FIXME:
-- A bug in Herbie causes it to sometimes output infinities,
-- which break this function and cause it to error.
fromCanonicalMathExpr :: (MathExpr,[(String,String)]) -> MathExpr
fromCanonicalMathExpr (e,xs) = go e
    where
        xs' = map (\(a,b) -> (b,a)) xs

        go (EMonOp op e1) = EMonOp op (go e1)
        go (EBinOp op e1 e2) = EBinOp op (go e1) (go e2)
        go (EIf (EBinOp "<" _ (ELeaf "-inf.0")) e1 e2) = go e2 -- FIXME: added due to bug above
        go (EIf cond e1 e2) = EIf (go cond) (go e1) (go e2)
        go (ELit r) = ELit r
        go (ELeaf str) = case lookup str xs' of
            Just x -> ELeaf x
            Nothing -> error $ "fromCanonicalMathExpr: str="++str++"; xs="++show xs'

-- | Calculates the maximum depth of the AST.
mathExprDepth :: MathExpr -> Int
mathExprDepth (EBinOp _ e1 e2) = 1+max (mathExprDepth e1) (mathExprDepth e2)
mathExprDepth (EMonOp _ e1   ) = 1+mathExprDepth e1
mathExprDepth _ = 0

--------------------------------------------------------------------------------
-- functions for manipulating math expressions in lisp form

getCanonicalLispCmd :: MathExpr -> (String,[(String,String)])
getCanonicalLispCmd me = (mathExpr2lisp me',varmap)
    where
        (me',varmap) = toCanonicalMathExpr me

fromCanonicalLispCmd :: (String,[(String,String)]) -> MathExpr
fromCanonicalLispCmd (lisp,varmap) = fromCanonicalMathExpr (lisp2mathExpr lisp,varmap)

-- | Converts MathExpr into a lisp command suitable for passing to Herbie
mathExpr2lisp :: MathExpr -> String
mathExpr2lisp = go
    where
        go (EBinOp op a1 a2) = "("++op++" "++go a1++" "++go a2++")"
        go (EMonOp op a) = "("++op++" "++go a++")"
        go (EIf cond e1 e2) = "(if "++go cond++" "++go e1++" "++go e2++")"
        go (ELeaf e) = e
        go (ELit r) = if (toRational (floor r::Integer) == r)
            then show (floor r :: Integer)
            else show (fromRational r :: Double)

-- | Converts a lisp command into a MathExpr
lisp2mathExpr :: String -> MathExpr
lisp2mathExpr ('-':xs) = EMonOp "negate" (lisp2mathExpr xs)
lisp2mathExpr ('(':xs) = if length xs > 1 && last xs==')'
    then case groupByParens $ init xs of
        [op,e1]             -> EMonOp op (lisp2mathExpr e1)
        [op,e1,e2]          -> EBinOp op (lisp2mathExpr e1) (lisp2mathExpr e2)
        ["if",cond,e1,e2]   -> EIf (lisp2mathExpr cond) (lisp2mathExpr e1) (lisp2mathExpr e2)
        _                   -> error $ "lisp2mathExpr: "++xs
    else error $ "lisp2mathExpr: malformed input '("++xs++"'"
lisp2mathExpr xs = case splitOn "/" xs of
    [num,den] -> lisp2mathExpr $ "(/ "++num++" "++den++")"
    _ -> case readMaybe xs :: Maybe Double of
        Just x -> ELit $ toRational x
        Nothing -> ELeaf xs

-- | Extracts all the variables from the lisp commands with no duplicates.
lisp2vars :: String -> [String]
lisp2vars = nub . lisp2varsNoNub

-- | Extracts all the variables from the lisp commands.
-- Each variable occurs once in the output for each time it occurs in the input.
lisp2varsNoNub :: String -> [String]
lisp2varsNoNub lisp
    = sort
    $ filter (\x -> x/="("
                 && x/=")"
                 && (x `notElem` binOpList)
                 && (x `notElem` monOpList)
                 && (head x `notElem` ("1234567890"::String))
             )
    $ tokenize lisp :: [String]
    where
        -- We just need to add spaces around the parens before calling "words"
        tokenize :: String -> [String]
        tokenize = words . concat . map go
            where
                go '(' = " ( "
                go ')' = " ) "
                go x   = [x]

lispHasRepeatVars :: String -> Bool
lispHasRepeatVars lisp = length (lisp2vars lisp) /= length (lisp2varsNoNub lisp)

-------------------------------------------------------------------------------
-- utilities

readMaybe :: Read a => String -> Maybe a
readMaybe = fmap fst . listToMaybe . reads

-- | Given an expression, break it into tokens only outside parentheses
groupByParens :: String -> [String]
groupByParens str = go 0 str [] []
    where
        go 0 (' ':xs) []  ret = go 0     xs []         ret
        go 0 (' ':xs) acc ret = go 0     xs []         (ret++[acc])
        go 0 (')':xs) acc ret = go 0     xs []         (ret++[acc])
        go i (')':xs) acc ret = go (i-1) xs (acc++")") ret
        go i ('(':xs) acc ret = go (i+1) xs (acc++"(") ret
        go i (x  :xs) acc ret = go i     xs (acc++[x]) ret
        go _ []       acc ret = ret++[acc]


