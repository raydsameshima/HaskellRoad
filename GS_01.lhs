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

Note; for later convinience,
  if n>1:: non prime, then (ld(n))^2 <= n,
is equivalent to its contraposition:
  if (ld(n))^2 > n, then n>1 :: prime.
     
m divides n <=> the remainder of the process of dividing n by m equals 0:

> divides :: Integer -> Integer -> Bool
> divides d n = (rem n d == 0)

It is convenient to define ld function in terms of a helper ldf, for the least divisor starting from a given threshold k <= n.
Thus
  ld(k)(n)
is the least divisor of n and ld(k)(n) >= k.

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

> removeFst :: Int -> [Int] -> [Int]
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
>   where sumOfList = toRational . sum' $ lst
>         lengthOfList = toRational . length' $ lst 

  *GS_01> :info average 
  average :: [Rational] -> Rational   -- Defined at GS_01.lhs:159:3

> sum' :: Num a => [a] -> a
> sum' [] = 0
> sum' (x:xs) = x + sum' xs
> length' :: Num a => [t] -> a
> length' [] = 0
> length' (x:xs) = 1 + length' xs

type synonym
  *GS_01> :info String
  type String = [Char]  -- Defined in ‘GHC.Base’

Exercise 1.13

> count :: Char -> String -> Int
> count _ [] = 0
> count s (t:ts) 
>   | s == t = 1+ count s ts
>   | otherwise = count s ts

Exercise 1.14
A function that converts a string to another:
  "bang!" -> "baannngggg!!!!!"

> helper :: (Int, Char) -> [Char]
> helper (n, c)
>   | n < 1     = [] 
>   | otherwise = c : (helper (n-1, c))

> blowup = concat . map helper . zip [1..]

Exiercise 1.15
A sort function in alphabetical order.

sortString :: [String] -> [String]
