module TUOLP

where

import TAMO

evens = [x | x <- [0..], even x]

isPrime :: Integer -> Bool
isPrime n 
 | n < 1     = error "not a positive integer"
 | n == 1    = False
 | otherwise = ldp n == n
  where
   ldp = ldpf primes
   ldpf (p:ps) m 
    | rem m p == 0 = p
    | p^2 > m      = m
    | otherwise    = ldpf ps m
   primes = 2:filter isPrime [3,5..]

-- the sieve of Eratosthenes
sieve :: [Integer] -> [Integer]
sieve (0:xs) = sieve xs
sieve (x:xs) = x : sieve (mark xs 1 x)
 where
  mark :: [Integer] -> Integer -> Integer -> [Integer]
  mark (y:ys) k m 
   | k == m    = 0 : (mark ys 1     m)
   | otherwise = y : (mark ys (k+1) m)

primes :: [Integer]
primes = 2: sieve [3,5..]

examles =
 [take n primes | n <- [0..], 
                  not (isPrime (product (take n primes) +1))
 ]

mernenne =
 [ (p, 2^p-1) | p <- primes, isPrime (2^p -1)]
notMersenne = 
 [ (p, 2^p-1) | p <- primes, not $ isPrime (2^p -1)]

pDivisors :: Integer -> [Integer]
pDivisors n =
 [ d | d <- [1..(n-1)], rem n d == 0] 

-- twin
primePairs :: [(Integer, Integer)]
primePairs =
 pairs primes
  where
   pairs (x:y:xys) 
    | x + 2 == y = (x,y) : pairs (y:xys)
    | otherwise  = pairs (y:xys)

primeTriples :: [(Integer, Integer, Integer)]
primeTriples =
 triples primes
  where
   triples (x:y:z:zs)
    | x + 2 == y && y + 2 == z = (x,y,z) : triples (y:z:zs)
    | otherwise                = triples (y:z:zs)
-- 三つ子素数は(3,5,7) のみで証明可能（3の倍数+0, +1, +2 で場合分け）

