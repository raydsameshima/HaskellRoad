-- SetOrd.hs
-- Sets as a ordered lists without duplicates.

module SetOrd ( 
  Set(..), 
  emptySet, 
  isEmpty, 
  inSet, 
  subSet, 
  insertSet, 
  deleteSet, 
  powerSet, 
  takeSet, 
  (!!!), 
  list2set, 
  unionSet
  )

where

import Data.List (sort)

newtype Set a = Set [a] deriving (Eq, Ord)

instance (Show a) => Show (Set a) where
  showsPrec _ (Set a) str = showSet a str

showSet [] str = showString "{}" str
showSet (x:xs) str = showChar '{' ( shows x ( showl xs str))
  where 
    showl [] str = showChar '}' str
    showl (x:xs) str = showChar ',' (shows x (showl xs str))

emptySet :: Set a
emptySet = Set []

isEmpty :: Set a -> Bool
isEmpty (Set []) = True
isEmpty _        = False

inSet :: (Ord a) => a -> Set a -> Bool
inSet x (Set s) = elem x (takeWhile (<= x) s)

subSet :: (Ord a) => Set a -> Set a -> Bool
subSet (Set []) _ = True
subset (Set (x:xs)) set = (inSet x set) && subSet (Set xs) set

insertSet :: (Ord a) => a -> Set a -> Set a
insertSet x (Set s) = Set (insertList x s)

insertList x [] = [x]
insertList x ys@(y:ys') = 
  case compare x y of
    GT -> y : insertList x ys'
    EQ -> ys
    _  -> x : ys

deleteSet :: Ord a => a -> Set a -> Set a
deleteSet x (Set s) = Set (deleteList x s)

deleteList x [] = []
deleteList x ys@(y:ys') =
  case compare x y of
    GT -> y : deleteList x ys'
    EQ -> ys'
    _  -> ys

list2set :: Ord a => [a] -> Set a
list2set [] = Set []
list2set (x:xs) = insertSet x (list2set xs)
-- list2set xs = Set (foldr insertList [] xs)

powerSet :: Ord a => Set a -> Set (Set a)
powerSet (Set xs) =
  Set (sort (map (\xs -> (list2set xs)) (powerList xs)))

powerList :: [a] -> [[a]]
powerList [] = [[]]
powerList (x:xs) = (powerList xs) ++ (map (x:) (powerList xs))

takeSet :: Eq a => Int -> Set a -> Set a
takeSet n (Set s) = Set (take n s)

infix 9 !!!
(!!!) :: Eq a => Set a -> Int -> a
(Set s) !!! n = s !! n

unionSet :: Ord a => Set a -> Set a -> Set a
unionSet (Set []) set2 = set2
unionSet (Set (x:xs)) set2 =
  insertSet x (unionSet (Set xs) set2)

