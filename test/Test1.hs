{-# LANGUAGE GADTs,RebindableSyntax,CPP #-}
module Main
-- module Test1
    where

import SubHask
import qualified Prelude as P
-- import Prelude as P

--------------------------------------------------------------------------------
-- type signature tests

#define f1(x1) (sqrt ((x1)+1) - sqrt (x1))

-- -- {-# NOINLINE test1 #-}
test1 :: (RationalField a, Real a) => a -> a
-- test1 :: (Real a, Floating a) => a -> a
-- test1 :: Float -> Float
-- test1 x1 = x1 + 1.1
test1 x1 = f1(x1)
-- test1 x1 = x1*sqrt x1
-- test1 x1 = fromRational (toRational (1.1::Float))

test2 :: Float -> Float
test2 x1 = 1.1+x1

test3 :: Float -> String
test3 x1 = show $ x1+x1+sqrt x1

test4 :: String -> String
test4 str = show $ x1+x1+sqrt x1
    where
        x1 = fromIntegral (length str) :: Float

test5 :: (Show a, Real a) => String -> a -> String
test5 str x1 = show $ f1(x1)

test6 :: (Show a, Real a) => a -> String -> String
test6 x1 str = show $ f1(x1)

test7 :: Semigroup a => a -> a
test7 x1 = x1+x1+x1+x1+x1

--------------------------------------------------------------------------------
-- main

main = do

--     P.putStrLn $ "types_Int  ="++show (types_Int   5)
--     P.putStrLn $ "types_Float="++show (types_Float 5)
    P.putStrLn $ "test1="++show (test1 (5::Float))
    P.putStrLn $ "test1="++show (test1 (5::Double))
    P.putStrLn $ "test2="++show (test2 (5::Float))
    P.putStrLn $ "test3="++show (test3 5)
    P.putStrLn $ "test5="++test5 "str" (5::Float)
    P.putStrLn $ "test5="++test5 "str" (5::Double)
    P.putStrLn $ "test6="++test6 (5::Float)  "str"
    P.putStrLn $ "test6="++test6 (5::Double) "str"
    P.putStrLn "done"
