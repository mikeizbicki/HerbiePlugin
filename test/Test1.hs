{-# LANGUAGE GADTs,RebindableSyntax #-}
module Main
-- module Test1
    where

import SubHask
import qualified Prelude as P
-- import Prelude as P

--------------------------------------------------------------------------------
-- type signature tests

----------------------------------------
-- these functions should be ignored

-- types_Int :: Int -> Int
-- types_Int x1 = 1+x1

----------------------------------------
-- these functions should be processed

-- types_Float :: Float -> Float
-- types_Float x1 = 1+x1
--
-- types_big1 :: (a -> Float) -> (a -> Float) -> (a -> Float)
-- types_big1 = undefined
--
-- types_big2 :: (Real a, VectorSpace a) => a -> a
-- types_big2 = undefined
--
-- types_many :: (a -> b) -> (a -> b) -> (a -> b)
-- types_many = undefined
--
-- types_diff1 :: a -> b
-- types_diff1 = undefined
--
-- types_diff2 :: Float -> Float -> Double
-- types_diff2 = undefined
--
-- types_diff3 :: (a -> b) -> (a -> b) -> (a -> c)
-- types_diff3 = undefined

--------------------------------------------------------------------------------

-- class Num a => Cat a where
--     foo :: a -> a
-- instance Cat Float where
--     foo = id
--
-- class Cat a => Dog a where
--     bar :: a -> a
--     bar2 :: a -> a
-- instance Dog Float where
--     bar = id
--     bar2 = id

-- {-# NOINLINE f #-}
-- f :: Ord a => a -> Bool
-- f x = x == x

{-# NOINLINE test1 #-}
test1 :: Real a => a -> a
-- test1 :: Floating a => a -> a
test1 x1 = sqrt (x1+1) - sqrt x1

test2 :: Float -> Float
test2 x1 = x1+x1+fart
    where
        fart=x1+x1+x1

--------------------------------------------------------------------------------
-- main

main = do

--     P.putStrLn $ "types_Int  ="++show (types_Int   5)
--     P.putStrLn $ "types_Float="++show (types_Float 5)
    P.putStrLn $ "test1="++show (test1 (5::Float))
    P.putStrLn $ "test2="++show (test2 (5::Float))
    P.putStrLn "done"
