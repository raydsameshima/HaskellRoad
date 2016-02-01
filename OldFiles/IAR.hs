module IAR where

import Data.List
import STAL (display)

-- natural number is either zero or a succ of some natural number
-- like a Church numeral
data Natural = Z | S Natural deriving (Eq, Show)

plus :: Natural -> Natural -> Natural
plus m Z = m
plus m (S n) = S (plus m n)

mult :: Natural -> Natural -> Natural
mult m Z = Z
mult m (S n) = (mult m n) `plus` m

expn :: Natural -> Natural -> Natural
expn m Z = (S Z)
expn m (S n) = (expn m n) `mult` m

leq Z _ = True
leq (S _) Z = False
leq (S m) (S n) = leq m n

foldn :: (a -> a) -> a -> Natural -> a
foldn h c Z = c -- initial case
foldn h c (S n) = h (foldn h c n)

exclaim = foldn ('!':) []

plus'   = foldn (\n -> S n)
mult' m = foldn (plus m) Z
expn' m = foldn (mult m) (S Z)

catalan :: Int -> Integer
catalan 0 = 1
catalan 1 = 1
catalan n = sum $ map (\(a,b)->a*b) $ zip (catalan' (n-1)) (reverse (catalan' (n-1)))
  where catalan' m = [catalan k | k <- [1..m]] 

data BinTree = L | N BinTree BinTree deriving Show -- Leaf or Node

makeBinTree :: Integer -> BinTree
makeBinTree 0 = L
makeBinTree n = N (makeBinTree (n-1)) (makeBinTree (n-1))

count :: BinTree -> Integer
count L = 1
count (N t1 t2) = 1 + count t1 + count t2

depth :: BinTree -> Integer
depth L = 0
depth (N t1 t2) = 1 + (max (depth t1) (depth t2))

balanced :: BinTree -> Bool
balanced L = True
balanced (N t1 t2) = balanced t1
                     && balanced t2
                     && depth t1 == depth t2

-- hanoi tower
data Peg = A | B | C
type Tower = ([Int], [Int], [Int])
