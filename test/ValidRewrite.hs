{-# LANGUAGE GADTs,RebindableSyntax,CPP,FlexibleContexts,FlexibleInstances,ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving,DeriveDataTypeable #-}
{-# OPTIONS_GHC -dcore-lint #-}
{-
 - This test suite ensures that the rewrites that HerbiePlugin performs
 - give the correct results.
 -}

module Main
    where

import SubHask

import System.IO
-- import Data.Complex
-- import Linear.Quaternion
-- import Linear.V3
-- import Linear.Vector

--------------------------------------------------------------------------------

test1a :: Double -> Double -> Double
test1a far near = -(2 * far * near) / (far - near)

{-# ANN test1b "NoHerbie" #-}
test1b :: Double -> Double -> Double
test1b far near = -(2 * far * near) / (far - near)

{-# ANN test1c "NoHerbie" #-}
test1c :: Double -> Double -> Double
test1c far near = if far < -1.7210442634149447e81
    then ((-2 * far) / (far - near)) * near
    else if far < 8.364504563556443e16
        then -2 * far * (near / (far - near))
        else ((-2 * far) / (far - near)) * near

--------------------

test2a :: Double -> Double -> Double
test2a a b = a + ((b - a) / 2)

{-# ANN test2b "NoHerbie" #-}
test2b :: Double -> Double -> Double
test2b a b = a + ((b - a) / 2)

--------------------

-- test3a :: Quaternion Double -> Quaternion Double -> Quaternion Double
-- test3a (Quaternion q0 (V3 q1 q2 q3)) (Quaternion r0 (V3 r1 r2 r3)) =
--     Quaternion (r0*q0+r1*q1+r2*q2+r3*q3)
--                (V3 (r0*q1-r1*q0-r2*q3+r3*q2)
--                    (r0*q2+r1*q3-r2*q0-r3*q1)
--                    (r0*q3-r1*q2+r2*q1-r3*q0))
--                ^/ (r0*r0 + r1*r1 + r2*r2 + r3*r3)
--
-- {-# ANN test3b "NoHerbie" #-}
-- test3b :: Quaternion Double -> Quaternion Double -> Quaternion Double
-- test3b (Quaternion q0 (V3 q1 q2 q3)) (Quaternion r0 (V3 r1 r2 r3)) =
--     Quaternion (r0*q0+r1*q1+r2*q2+r3*q3)
--                (V3 (r0*q1-r1*q0-r2*q3+r3*q2)
--                    (r0*q2+r1*q3-r2*q0-r3*q1)
--                    (r0*q3-r1*q2+r2*q1-r3*q0))
--                ^/ (r0*r0 + r1*r1 + r2*r2 + r3*r3)

--------------------------------------------------------------------------------

-- asinh_ :: Complex Double -> Complex Double
-- asinh_ x = log (x + sqrt (1.0+x*x))
--
-- acosh_ :: Complex Double -> Complex Double
-- acosh_ x = log (x + (x+1.0) * sqrt ((x-1.0)/(x+1.0)))

atanh_ :: Double -> Double
atanh_ x = 0.5 * log ((1.0+x) / (1.0-x))

--------------------------------------------------------------------------------

#define mkTest(f1,f2,a,b) \
    putStrLn $ "mkTest: " ++ show (f1 (a) (b)); \
    putStrLn $ "mkTest: " ++ show (f2 (a) (b)); \
    putStrLn ""

#define mkTestB(f1,f2,a) \
    putStrLn $ "mkTest: " ++ show (f1 (a)); \
    putStrLn $ "mkTest: " ++ show (f2 (a)); \
    putStrLn ""

main = do
    mkTest(test1a,test1b,-2e90,6)
    mkTest(test1a,test1b,3,4)
    mkTest(test1a,test1b,2e90,6)

    mkTest(test1a,test1c,-2e90,6)
    mkTest(test1a,test1c,3,4)
    mkTest(test1a,test1c,2e90,6)

    mkTest(test2a,test2b,1,2)

--     mkTest(test3a,test3b,(Quaternion 1 (V3 1 2 3)),(Quaternion 2 (V3 2 3 4)))

--     mkTestB(asinh,asinh_,5e-17::Complex Double)
--     mkTestB(acosh,acosh_,5e-17::Complex Double)
    mkTestB(atanh,atanh_,5e-17::Double)

    putStrLn "done"





