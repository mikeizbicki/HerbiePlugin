module Stabalize.MathExpr
    where

-- | Stores the AST for a math expression in a generic form that requires no knoledge of Core syntax.
data MathExpr
    = EBinOp String MathExpr MathExpr
    | EMonOp String MathExpr
    | ELeaf String
    deriving Show

-- | Converts MathExpr into a lisp command suitable for passing to Herbie
mathExpr2lisp :: MathExpr -> String
mathExpr2lisp = go
    where
        go (EBinOp op a1 a2) = "("++op++" "++go a1++" "++go a2++")"
        go (EMonOp op a) = "("++op++" "++go a++")"
        go (ELeaf e) = e

-- | Converts a lisp command into a MathExpr
str2mathExpr :: String -> MathExpr
str2mathExpr ('(':xs) = if length xs > 1 && last xs==')'
    then case groupByParens $ init xs of
        [op,e1]    -> EMonOp op (str2mathExpr e1)
        [op,e1,e2] -> EBinOp op (str2mathExpr e1) (str2mathExpr e2)
    else error $ "str2mathExpr: malformed input '("++xs++"'"
str2mathExpr xs = ELeaf xs

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


