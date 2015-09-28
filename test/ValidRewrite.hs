{-# LANGUAGE GADTs,RebindableSyntax,CPP,FlexibleContexts,FlexibleInstances,ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving,DeriveDataTypeable #-}
{-
 - This test suite ensures that the rewrites that HerbiePlugin performs
 - give the correct results.
 -}

module Main
    where

import SubHask
import System.IO

--------------------------------------------------------------------------------

test1a :: Double -> Double -> Double
test1a far near = -(2 * far * near) / (far - near)

{-# ANN test1b "NoHerbie" #-}
test1b :: Double -> Double -> Double
test1b far near = -(2 * far * near) / (far - near)

test2a :: Double -> Double -> Double
test2a a b = a + ((b - a) / 2)

{-# ANN test2b "NoHerbie" #-}
test2b :: Double -> Double -> Double
test2b a b = a + ((b - a) / 2)

--------------------------------------------------------------------------------

#define mkTest(f1,f2,a,b) \
    putStrLn $ "mkTest: " ++ show (f1 (a) (b)); \
    putStrLn $ "mkTest: " ++ show (f2 (a) (b)); \
    putStrLn ""

main = do
    mkTest(test1a,test1b,-2e90,6)
    mkTest(test1a,test1b,0,6)
    mkTest(test1a,test1b,2e90,6)

    mkTest(test2a,test2b,1,2)





