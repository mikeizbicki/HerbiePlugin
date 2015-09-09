{-# LANGUAGE GADTs,RebindableSyntax,CPP,FlexibleContexts,FlexibleInstances #-}
module Main
-- module Test1
    where

import SubHask
import qualified Prelude as P
-- import Prelude as P

--------------------------------------------------------------------------------
-- type signature tests

-- #define f1(x1) (sqrt ((x1)+1) - sqrt (x1))

{-
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

-}

--------------------------------------------------------------------------------

{-
-- example1 :: Float -> Float -> Float
-- example1 x1 x2 = sqrt (x1*x1 + x2*x2)

-- example2 x = exp(log(x)+8)
--
-- example3 x = sqrt(x*x +1) -1
--
-- example4 x = exp(x)-1
--
-- example5 x = log(1+x)
--
-- example6 x y = sqrt(x+ y) - sqrt(y)

-- example7 k r a = k*(r-a)^3
--
-- example8 k r a = k*(r-a)^2

example9 x y = sin(x - y)

example10 p1x p2x p1y p2y = sqrt((p1x - p2x) * (p1x - p2x) + (p1y - p2y) * (p1y - p2y))

example11 x = sin(x)-x

example12 x = 1-cos(x)

-- example13 x1 x2 = sqrt((x1 - x2) * (x1 - x2))

example14 x y z = sqrt(x*x + y*y + z*z)

example15 x y z c = sqrt(x*x + y*y + z*z)/c

example16 tdx dx tdy dy = (tdx * dx + tdy * dy) / (dx * dx + dy * dy)

example17 tdx dx tdy dy sl2 = (tdx * dx + tdy * dy) / sl2

example18 x = (x + 0.1)-x

example19 x = log(x) - sin(x+1)

example20 a b = exp(1+log(a) + log(b))

example21 x = (1+sqrt(x-1))/(x-1)^2

example22 x = (1+sqrt(x))/(x-1)^2

example23 a b c d e f = a+b+(((d-c)*(d-c))*e*f/(e+f))

example24 q = sqrt(q*(q-1))

example25 a = sqrt(a^2-1)

example26 a b c d = ((a*b)+(c*d))/(a+c)

-- example27 x = sqrt(x^2)

example28 x y = sqrt(x) * y * y

example29 x y z = sqrt(x*x+y*y+z*z)

example30 x y = 1.75 * x * y*y + sqrt(x/y)

-- example31 x = exp(3*log(x)+2)

example32 x = exp(2*log(x))

example33 x = sqrt(1/x + 1) - sqrt(1/x)

example34 left i right count = left + i * ((left - right) / count)

example35 left right count = left + count * ((left - right) / count)

-- example36 x y = sqrt(x*x) - sqrt(y*y)

example37 x = log(x+1)-log(x)

example38 x = log(x+1)^x

example39 minval minstep val = (minval/minstep + val) * minstep

example40 x = x*x*cos(x/2 - sqrt(x))

-- example41 x4 = sqrt(x4^5) - sqrt(2)

example41 x = sqrt(4+x^2+x)

example42 x y z = x / sqrt(x*x + y*y + z*z)

example43 x = sin(sqrt(x+1))

example44 x = sqrt(x-2)-sqrt(x*x-3)

example45 x = (sin(x) - tan(x)) / x

example46 x y = 1 / sqrt(x^2 - y^2)

-- example47 x1 x2 = sqrt((x1 - x2)^2)

example48 x = x - sin(x)

example49 x = sqrt(x + 1) - 1 + x

example50 a b c = (a*a - c*c)/b

example51 x y = sin(x+y)-cos(x+y)

-- example52 x = (x + 1)^2 - 1

example53 x = sqrt(1+x) - sqrt(x)

example54 x = sqrt(x + 1) / (x*x)

example55 x = sqrt(x^2 / 3)

example56 a b = 100*(a-b)/a

-- example57 x = abs(x^3)-x^3

example58 x = log(x) - log(x+1)

example59 x = 1/x - 1/(x+1)

example60 a b c = -b + sqrt(b*b-4*a*c)/(2*a)

example61 a c an cn = log(exp(a)*an + exp(c)*cn) - log(an+cn)

example62 x = sqrt(sin(x)) - sqrt(x)

example63 x = log(1+x)

example64 a b = a * b / (1 - b + a * b)

example65 a b = b*sqrt(a * a + 1.0)

-- example66 x y = x * y * x*pi/y

example67 x = sqrt(x + 1) - sqrt(x - 1)

-- example68 x = cos(x + 1) * x^2

example69 a b = b*(a/b - log(1 + a/b))

example70 a b = b*(a/b - 1 - log(a/b))

-- example71 x = (6/(x^99))*(x^101)

example72 x = (1/(x^99))*(x^101)

example73 x = (1/(x^100))*(x^100)

example74 x y z = cos(sqrt(x*x+y*y+z*z))

example75 x = sqrt(sqrt(x*x+1)+1)

example76 a k = a + sqrt(a*a-k)

example77 a k = -a - sqrt(a*a-k)

example78 a b x = x*x*a+x*(a+b) +x*b

-- example79 x = (x + x) ^ 3 / x

example80 x = sqrt(x+1)-sqrt 1

-- example81 x = (x+1)-x

example82 x = sqrt(x+100)-sqrt(x)

example83 x = 1-cos(x)

example84 u v = sqrt(sqrt(u^2 + v^2) - u)

example85 x = exp(log(x))

example86 x = sqrt(x + 1) - sqrt(x) + sin(x - 1)

example87 x = exp x / sqrt(exp x - 1) * sqrt x

example88 x = (exp(x) - 1) / x

example89 x = sqrt(x + 2) - sqrt(x)
-}

--------------------------------------------------------------------------------

test :: Real x => x -> x -> x
test x y = y*x+1

--------------------------------------------------------------------------------
-- main


main = do
    P.putStrLn $ show $ test (5::Float) (2::Float)

--     P.putStrLn $ show $ example87 (5::Float)
--     P.putStrLn $ show $ example88 (5::Float)
--     P.putStrLn $ show $ example89 (5::Float)

--     P.putStrLn $ "example1="++show (example1 2 3::Float)
--     P.putStrLn $ "example1="++show (example1 3 2::Float)
--     P.putStrLn $ "example1="++show (example1 4 1::Float)

--     P.putStrLn $ "types_Int  ="++show (types_Int   5)
--     P.putStrLn $ "types_Float="++show (types_Float 5)
--     P.putStrLn $ "test1="++show (test1 (5::Float))
--     P.putStrLn $ "test1="++show (test1 (5::Double))
--     P.putStrLn $ "test2="++show (test2 (5::Float))
--     P.putStrLn $ "test3="++show (test3 5)
--     P.putStrLn $ "test5="++test5 "str" (5::Float)
--     P.putStrLn $ "test5="++test5 "str" (5::Double)
--     P.putStrLn $ "test6="++test6 (5::Float)  "str"
--     P.putStrLn $ "test6="++test6 (5::Double) "str"
    P.putStrLn "done"
