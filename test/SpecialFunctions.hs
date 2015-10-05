{-# LANGUAGE GADTs,RebindableSyntax,CPP,FlexibleContexts,FlexibleInstances,ConstraintKinds #-}
{-# OPTIONS_GHC -dcore-lint #-}

{-
 - This test suite demonstrates that the special functions `log1p`, `expm1`, and `hypot` all work.
 -}
module Main
    where

-- import SubHask
import Prelude as P

fromRational = P.fromRational

(<) :: Ord a => a -> a -> Bool
(<) = (P.<)

--------------------------------------------------------------------------------

test1 :: Floating a => a -> a -> a
test1 a b = sqrt (a*a + b*b)

-- test2 :: Double -> Double
-- test2 a = log (1 + a)
--
-- test3 :: Double -> Double
-- test3 a = exp a - 1

--------------------------------------------------------------------------------

main = return ()
