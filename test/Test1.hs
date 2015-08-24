{-# LANGUAGE GADTs #-}
module Main
    where

import SubHask
import qualified Prelude as P
-- import Prelude as P

test1 :: Float -> Float
test1 x1 = sqrt (x1+1) - sqrt x1

main = do
    P.putStrLn $ "test1="++show (test1 5)
