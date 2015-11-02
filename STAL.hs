module STAL

where

import Data.List
import DB

naturals = [0..]
evens1 = [n | n <- naturals, even n]
odds1  = [n | n <- naturals, odd  n]
evens2 = [2*n | n <- naturals]

small_squares1 = [n^2 | n <- [0..999]]
small_squares2 = [n^2 | n <- naturals, n < 1000]
-- n <- naturals のせいでまずinfinite list が作られるので
-- small_squares2 はlist の生成が終わらない
-- リスト内包表記（List comprehension）では遅延評価ではないらしい
-- つまりリストの中の評価は正格ということかな
-- 試しに条件部分を入れ替えるとインタープリタはn が何かわからずエラーを吐く
--small_squares3 = [n^2 | n < 1000, n <- naturals]

-- Collatz problem
run :: Integer -> [Integer]
run n 
 | n < 1     = error "argument should be positive"
 | n == 1    = [1]
 | even n    = n : run (div n 2)
 | otherwise = n : run (3*n + 1)

myReverse :: [a] -> [a]
myReverse [] = []
myReverse (x:xs) = (myReverse xs) ++ [x]

splitList :: [a] -> [([a], [a])]
splitList [x,y] = [([x],[y])]
splitList (x:y:zs) = ([x],(y:zs)): addLeft x (splitList (y:zs))
  where addLeft u [] = []
        addLeft u ((vs,ws):rest) = (u:vs,ws): addLeft u rest

-- section 4.7 List comprehension and database query
characters = nub [ x | ["play", _, _, x] <- db ]
movies     =     [ x | ["release", x, _] <- db ]
actors     = nub [ x | ["play", x, _, _] <- db ]
directors  = nub [ x | ["direct", x, _ ] <- db ]
dates      = nub [ x | ["release", _, x] <- db ]
universe = nub (characters ++ actors ++ directors ++ movies ++ dates)

-- list comprehensions
direct = [ (x,y) | ["direct", x, y] <- db]
act = [ (x,y) | ["play", x, y, _] <- db]
play = [ (x,y,z) | ["play",x,y,z] <- db]
release = [ (x,y) | ["release", x,y] <- db]

charP = \x -> elem x characters
actorP = \x -> elem x actors
movieP = \x -> elem x movies
directorP = \x -> elem x directors
dataP = \x -> elem x dates
actP = \(x,y) -> elem (x,y) act
releaseP = \(x,y) -> elem (x,y) release
directP = \(x,y) -> elem (x,y) direct
playP = \(x,y,z) -> elem (x,y,z) play

-- "Give me the actors that also are directors."
q1 = [ x | x <- actors, directorP x]
q2 = [ (x,y) | (x,y) <- act, directorP x]
q3 = [ (x,y,z) | (x,y) <- direct, (y,z) <- release ]
q4 = [ (x,y,z) | (x,y) <- direct, (u,z) <- release, y == u ]
q5 = [ (x,y) | (x,y) <- direct, (u,"1995") <- release, y == u]


addElem :: a -> [[a]] -> [[a]]
addElem x = map (x:)

powerList :: [a] -> [[a]]
powerList [] = [[]]
powerList (x:xs) = (powerList xs) ++ (map (x:) (powerList xs))

powerList' x = sort $ powerList x

data S = Void deriving (Eq, Show)
empty :: [S]
empty = []


display :: Int -> String -> IO ()
display n str = putStrLn (display' n 0 str)
  where 
  display' _ _ [] = []
  display' n m (x:xs) | n == m    = '\n': display'  n   0  (x:xs)
                      | otherwise =  x  : display'  n (m+1)  xs 
