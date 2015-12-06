GS_01.lhs

The Haskell Road to Logic, Maths and Programming
http://homepages.cwi.nl/~jve/HR/

"There is no royal road to mathematics."
by the mathematician Menaechmus

Haskell, a member of the Lisp family.
Haskell is based  on a logical theory of computable functions called the lambda calculus.

Lambda calculus is a formal language capable of expressing arbitrary computable functions.
In combination with types it forms a compact way to denote on the one hand functional programs and on the other hand mathematical proofs.[Bar84]

Haskell can be viewed as a particularly elegant implementation of the lambda calculus.

> module GS_01 where

1. Getting Started
1.1 Starting up the Haskell Interpreter
1.2 Implementing a Prime Number Test

Let n>1 be a natural number.
Define 
  ld(n) 
for the least (smallest) natural number greater than 1 that divides n, i.e. there exists some number a s.t.
  a*d = n.
Note that ld(n) exists for every natural number n>1, simply n itself divide itself.
Therefore, the set of all divisors of n that are greater than 1 is non-empty, and there is a least element.

Proposition 1.2
1. If n>1, then ld(n) is prime.
2. If n>1 and n is not prime, then (ld(n))^2 <= n.

Proof
1. (by contradiction)
Suppose ld(n) is NOT prime, then there are natural numbers a,b >1  s.t.
  ld(n) = a*b
Then clearly,
  1 < a,b < ld(n),
and a, b divide n.
Since we define ld(n) is the smallest divisor of n, with ld(n)>1.
Thus ld(n) must be a prime number.

2. Suppose n>1 and n is not prime.
Then there exists a>1 s.t.
  n = a*ld(n),
and
  1 < ld(n) <= a < n
since ld(n) is the smallest divisor.
Therefore,
  (ld(n))^2 = ld(n) * ld(n) <= ld(n) * a = n.

Q.E.D.

Note; for later convenience,
  if n>1:: non prime, then (ld(n))^2 <= n,
is equivalent to its contraposition:
  if (ld(n))^2 > n, then n>1 :: prime.
     
m divides n <=> the remainder of the process of dividing n by m equals 0:

> divides :: Integer -> Integer -> Bool
> divides d n = (rem n d == 0)

It is convenient to define ld function in terms of a helper ldf, for the least divisor starting from a given threshold k <= n.

{-
Thus
  ldf(k)(n)
is the least divisor of n and ld(k)(n) >= k.
-}
"Thus, ldf(k)(n) is the least divisor of n, provided n has no divisors <k."

> ld :: Integer -> Integer
> ld n = ldf 2 n
> ldf :: Integer -> Integer -> Integer
> ldf k n
>   | k `divides` n = k
>   | k^2 > n       = n
>   | otherwise     = ldf (k+1) n

The 1st line of the guard handles the case where the 1st argument(k) divides the 2nd argument(n).
The 2nd line handles the case where k does not divide n, and k^2>n, and the 3rd line is the case where k does not divide n and k^2<n.

The follwing is our first implementation of the test for being a prime number:

> prime0 :: Integer -> Bool
> prime0 n
>   | n < 1     = error "not a positive integer"
>   | n == 1    = False
>   | otherwise = (ld n == n)

  *GS_01> filter prime0 [1..100]
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

1.3 Haskell Type Declarations
type class (Integral)
  *GS_01> :type rem
  rem :: Integral a => a -> a -> a

1.4 Identifiers in Haskell
1.5 Playing the Haskell Game

Example 1.8
A function that gives the minimum of a list of integers:

> mnmInt :: [Int] -> Int
> mnmInt []     = error "empty list []!"
> mnmInt [x]    = x
> mnmInt (x:xs) = min' x (mnmInt xs)
>   where min' :: Int -> Int -> Int
>         min' x y
>           | x <= y    = x
>           | otherwise = y

  *GS_01> minBound :: Int
  -9223372036854775808
  *GS_01> maxBound :: Int
  9223372036854775807
  *GS_01> 2^63 -1
  9223372036854775807

Exercise 1.9

> maxInt:: [Int] -> Int
> maxInt [] = error "empty list []!"
> maxInt [x] = x
> maxInt (x:xs) = max' x (maxInt xs)
>   where max' x y
>           | x <= y    = y
>           | otherwise = x

Exercise 1.10
A function removeFst that removes the first occurence of an integer m from a list of integers.

> -- removeFst :: Int -> [Int] -> [Int]
> removeFst :: Ord a => a -> [a] -> [a]
> removeFst m [] = error "empty list[]!"
> removeFst m [n] 
>   | m == n    = []
>   | otherwise = [n]
> removeFst m (n:ns)
>   | m == n    = ns
>   | otherwise = n : removeFst m ns

Exercise 1.11
A sort algorithm:
  an empty list is already sorted,
  for a non-empty list, we put the minimum in front of the result of sorting the list that results from removing its minimum.

> srtInts :: [Int] -> [Int]
> srtInts []   = []
> -- srtInts [n]  = [n]
> srtInts list = min : sortedSubList
>   where min = mnmInt list
>         sortedSubList = srtInts $ removeFst min list

[n] case does not need.

Example 1.12
A function that calculates the average of a list of numbers.

> average [] = error "empty list[]!"
> average [n] = n
> average lst = sumOfList / lengthOfList
>   where sumOfList = toRational . sum $ lst
>         lengthOfList = toRational . length $ lst 

  *GS_01> :info average 
  average :: [Rational] -> Rational   -- Defined at GS_01.lhs:159:3

> sum' :: Num a => [a] -> a
> sum' [] = 0
> sum' (x:xs) = x + sum' xs

> length' :: [a] -> Int
> length' [] = 0
> length' (x:xs) = 1 + length' xs

> length'' :: [a] -> Int
> length'' = sum . map' (\_ -> 1) 

type synonym
  *GS_01> :info String
  type String = [Char]  -- Defined in ‘GHC.Base’

Exercise 1.13

> count :: Char -> String -> Int
> count _ [] = 0
> count s (t:ts) 
>   | s == t    = 1 + count s ts
>   | otherwise = count s ts

Exercise 1.14
A function that converts a string to another:
  "bang!" -> "baannngggg!!!!!"

> helper :: (Int, Char) -> [Char]
> helper (n, c)
>   | n < 1     = [] 
>   | otherwise = c : (helper (n-1, c))

> blowup :: String -> String
> blowup = concat . map helper . zip [1..]

Of course, we can use the naive recursions:

> blowup' :: String -> String
> blowup' lst = f lst 1
>   where f [] _ = []
>         f (x:xs) n = helper (n, x) ++ (f xs (n+1))

Exercise 1.15
A sort function in alphabetical order.

> -- sortString :: [String] -> [String]
> sortString [] = []
> sortString (x:xs) = left ++ right
>   where left = sortString [y| y<- xs, y<x] 
>         right= x:( sortString [y| y<- xs, y>=x])

This is actually the quicksort!

Naively, we should use the following implementations.
mnm function will find the minimum element of the list of Ord instances.

> mnm :: Ord a => [a] -> a
> mnm [] = error "empty list"
> mnm [x] = x
> mnm (x:xs) = min x (mnm xs) 

Using mnm, our sort function becomes 

> sort :: Ord a => [a] -> [a]
> sort [] = []
> sort xs = minElement : restList
>   where minElement = mnm xs 
>         restList = sort $ removeFst minElement xs  

bubble sort?

Exercise 1.16
Another isPrefix function.

> prefix :: String -> String -> Bool
> prefix [] _ = True
> prefix _ [] = False
> prefix (x:xs) (y:ys) = (x==y) && prefix xs ys

Exercise 1.17
Another isSubString function.

> substring :: String -> String -> Bool
> substring [] _ = True
> substring _ [] = False
> substring xs all@(y:ys) = prefix xs all || substring xs ys

1.6 Haskell Types
Exercise 1.18
... easy

Exercise 1.19
  *GS_01> :type head
  head :: [a] -> a
  *GS_01> :type last
  last :: [a] -> a
  *GS_01> :type init
  init :: [a] -> [a]
  *GS_01> :type fst
  fst :: (a, b) -> a
  *GS_01> :type (++)
  (++) :: [a] -> [a] -> [a]
  *GS_01> :type flip
  flip :: (a -> b -> c) -> b -> a -> c
  *GS_01> :type flip (++)
  flip (++) :: [a] -> [a] -> [a]

1.7 The Prime Factorization Algorithm
Let n>1 be a natural number.
The pseudo code of prime factorization is
  WHILE n =/ 1 DO BEGIN p:=ld(n); n:= n/p END
As we have seen, ld(n) exists and is prime.
This algorithm will terminate, since through the loop will decrease n.

> factors :: Integer -> [Integer]
> factors n
>   | n < 1     = error "argument not positive"
>   | n == 1    = []
>   | otherwise = p: factors (n `div` p)
>       where p = ld n

1.8 The map and filter Functions
An introduction to higher order functions, or functionals.

> map' :: (a -> b) -> [a] -> [b]
> map' f []     = []
> map' f (x:xs) = (f x) : map' f xs   

Exercise 1.20
Write lengths that takes a list of lists and returns the the sum of their lengths using map.

> lengths :: [[a]] -> [Int]
> lengths = map length'

Exercise 1.21
Use map to write a function sumLengths that takes a list of lists and return the sum of their lengths.

> sumLengths, sumLengths' :: [[a]] -> Int
> sumLengths = sum . map length'
>
> sumLengths' = sum . lengths

> filter' :: (a -> Bool) -> [a] -> [a]
> filter' p [] = []
> filter' p (a:as) 
>   | p a       = a : filter' p as
>   | otherwise = filter' p as

Example 1.22
This is an infinite list of primes that filters from [2..].

> primes0 :: [Integer]
> primes0 = filter prime0 [2..]

  *GS_01> take 10 primes0
  [2,3,5,7,11,13,17,19,23,29]

Example 1.23
An improvement of ld.
The helper function ldf checks k|n for all k with
  2 <= k <= sqrt(n)
by +1 step.
In fact, it is enough to check p|n for the primes p with
  2 <= p <= sqrt(n).

> ldp :: Integer -> Integer
> ldp n = ldpf primes1 n
> ldpf :: [Integer] -> Integer -> Integer
> ldpf (p:ps) n
>   | n `rem` p == 0 = p
>   | p^2 > n        = n
>   | otherwise      = ldpf ps n

The prime list (p:ps) is an example of lazy list, because we compute only the part of the list that we need for further processing.
To define primes1 we need a test for primality, but that test is itself defined in terms of the function ld, which in turn refers to primes1.
We seem to be running around in a "circle".

> primes1 :: [Integer]
> primes1 = 2 : filter prime [3,5..]

> prime :: Integer -> Bool
> prime n
>   | n < 1     = error "not a positive integer"
>   | n == 1    = False
>   | otherwise = (ldp n == n)
  
  *GS_01> :set +s
  *GS_01> take 10000 primes0
  (13.45 secs, 2,751,947,128 bytes)
  *GS_01> take 10000 primes1
  (3.36 secs, 617,355,280 bytes)

About 4 times faster.

Exercise 1.24
The point-free style.

1.9 Haskell Equations and Equational Reasoning
1.10 Further Reading

