module REL where

import Data.List
import SetOrd

divisors :: Integer -> [(Integer, Integer)]
divisors n = [ (d, quot n d) | d <- [1..k], rem n d == 0]
  where k = floor (sqrt (fromInteger n))

divs :: Integer -> [Integer]
divs n = (fst list) ++ reverse (snd list)
  where list = unzip (divisors n)

properDivs :: Integer -> [Integer]
properDivs n = init (divs n)

perfect :: Integer -> Bool
perfect n = sum (properDivs n) == n

perfectNums :: Integer -> [Integer]
perfectNums k = [n | n <- [1..k], perfect n]

type Rel a = Set (a,a)
domR, ranR :: Ord a => Rel a -> Set a
domR (Set r) = list2set [x| (x,_) <- r]
ranR (Set r) = list2set [y| (_,y) <- r]

idR :: Ord a => Set a -> Rel a
idR (Set xs) = Set [(x,x) | x <- xs]

totalR :: Set a -> Rel a
totalR (Set xs) = Set [(x,y) | x <- xs, y <- xs]

invR :: Ord a => Rel a -> Rel a
invR (Set []) = Set []
invR (Set ((x,y):r)) = insertSet (y,x) (invR (Set r))

inR :: Ord a => Rel a -> (a,a) -> Bool
inR r (x,y) = inSet (x,y) r

complR :: Ord a => Set a -> Rel a -> Rel a
complR (Set xs) r =
  Set [(x,y) | x <- xs, y <- xs, not (inR r (x,y))]

reflR, irreflR :: Ord a => Set a -> Rel a -> Bool
reflR set r = subSet (idR set) r
irreflR (Set xs) r = 
  all (\pair -> not (inR r pair)) [(x,x) | x <- xs]

symR :: Ord a => Rel a -> Bool
symR (Set []) = True
symR (Set ((x,y):pairs) 
  | x == y = symR (Set pairs)
  | otherwise = inSet (y,x) (Set pairs) 
                && symR (deleteSet (y,x) (Set pairs))


