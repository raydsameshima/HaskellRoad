module FCT where

import Data.List

f x = x^2 + 1
--g = \x-> x^2 + 1
absReal x
  | x >= 0    = x
  | otherwise = -x

{-id :: a -> a
id x = x
-}
-- function as a graph
list2fct :: Eq a => [(a,b)] -> a -> b
list2fct [] _ = error "function not total"
list2fct ((u,v):uvs) x 
  | x == u    = v
  | otherwise = list2fct uvs x

fct2list :: (a -> b) -> [a] -> [(a,b)]
fct2list f xs = [(x, f x) | x <- xs]

ranPairs :: Eq b => [(a,b)] -> [b]
ranPairs f = nub [y | (_,y) <- f]

-- If the domain of the function is bounded,
listValues :: Enum a => (a -> b) -> a -> [b]
listValues f i = (f i) : listValues f (succ i)
listRange :: (Bounded a, Enum a) => (a -> b) -> [b]
listRange f = [f i | i <- [minBound..maxBound]]

before :: (a -> b) -> (b -> c) -> (a -> c);
(f `before` g) x = g (f x)
