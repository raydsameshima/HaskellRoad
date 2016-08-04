WWN_08.lhs

Working with Numbers

> module WWN_08 where

> import Data.List
> import Nats

8.1 A Module for Natural Numbers

> binary :: Integral a => a -> [Int]
> binary x = reverse $ bits x
>   where
>     bits 0 = [0]
>     bits 1 = [1]
> --  bits n = toInt' (rem n 2): bits (quot n 2)

8.2 GCD and the Fundamental Theorem of Arithmetic
Euclid's GCD algorithm

> myGcd :: Integral a => a -> a -> a
> myGcd 0 0 = 0
> myGcd x y
>   | x < 0 = myGcd (-x) y
>   | y < 0 = myGcd x (-y)
> myGcd x y 
>   | x == y = x
>   | x <  y = myGcd (y-x) x
>   | otherwise = myGcd y x

Exercise 8.2

> coprime :: Integral a => a -> a -> Bool
> coprime m n = 1 == (gcd m n)

Theorem 8.4
For all positive a,b \in N, there are integers m,n with
  m*a+n*b == gcd a b

