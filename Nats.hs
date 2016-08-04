-- Nats.hs

module Nats where

import Data.Ratio ((%))

data Natural = Z
             | S Natural
             deriving (Eq, Show)

instance Ord Natural where
  compare Z Z = EQ
  compare Z _ = LT
  compare _ Z = GT
  compare (S m) (S n) = compare m n

instance Enum Natural where
  succ n = S n
  pred Z     = Z -- "cut-off"
  pred (S n) = n
  -- toEnum   = fromInt -- :: Int -> Natural
  toEnum 0 = Z
  toEnum m = toEnum' m Z
    where
      toEnum' 0 n = n
      toEnum' m n = toEnum' (m-1) (S n)
  -- fromEnum = toInt   -- :: Natural -> Int
  fromEnum Z = 0
  fromEnum n = fromEnum' n 0
    where
      fromEnum' Z m = m
      fromEnum' (S n) m = fromEnum' n (m-1)

  enumFrom n = map toEnum [(fromEnum n)..]

instance Num Natural where
  (+) = foldn succ
  (*) = \m -> foldn (+m) Z
  (-) = foldn pred
  abs = id         -- Natural is not negative
  signum Z = Z
  signum n = (S Z) -- One
  fromInteger n
    | n <  0    = error "fromInteger: no negative naturals"
    | n == 0    = Z
    | otherwise = S (fromInteger (n-1))

foldn :: (a -> a) -> a -> Natural -> a
foldn h c Z     = c
foldn h c (S n) = h (foldn h c n)

instance Real Natural where
  toRational x = toInteger x % 1
 
instance Integral Natural where
  quotRem n d
    | d > n     = (Z,n)   
    | otherwise = (S q, r)
    where
      (q,r) = quotRem (n-d) d
  toInteger = foldn succ 0
