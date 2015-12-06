TUOLP_03.lhs

3. The Use of Logic: Proof
... this section also illustrates how the computer can be used (sometimes) as an instrument for checking particular cases, and therefore as a tool for refuting general claims.

> module TUOLP_03 where

> import TAMO_02

3.1 Proof Style
3.2 Proof Recipes
3.3 Rules for Connectives
3.4 Rules for the Quantifiers
3.5 Summary of the Proof Recipes
3.6 Some Strategic Guidelines

3.7 Reasoning and Computation with Primes
In this section we'll demonstrate the use of the computer for investigating the theory of prime numbers.
'(prime) of prime' is for later convenience.

> prime :: Integer -> Bool
> prime n 
>   | n < 0     = error "not a positive"
>   | n == 1    = False
>   | otherwise = ldp n == n
>
> ldp = ldpf primes
> ldpf (p:ps) m
>   | rem m p == 0 = p
>   | p^2 > m      = m
>   | otherwise    = ldpf ps m
>
> primes' = 2: filter prime [3,5..]

Theorem 3.33 (Euclid)
There are infinitely many prime numbers.

Exercise 3.34
Show that
  A := [4*n + 3| n<-[0..]]
contains infinitely many primes.

Proof
Let us assume there are only finitely many primes in A:
  A = [p(1),p(2)... p(n)| p(i) = 4*n(i) + 3, i<-[1..n]]
Consider the following number N
  N := 4*p(1)* ... *p(n) -1
    =  4*(p(1)* ... *p(n) -1) + 3
Clearly N is an odd number and N does not have p's as its factors.
If N is prime, we have a contradiction.
Otherwise N has a prime factor q, different from all p's.
  N = q * N'
Now, q>2 has the form either
  4*r + 1 or 4*r + 3
If q = 4*r + 3 then done, since q in not in A; a contradiction.
So it suffices to consider q = 4*r + 1 form.
Since
  (4*a+1)*(4*b+1) = 4*(4*a*b + a + b) + 1
we can assume
  N = q * N'
    = (4*r+1)*(4*s+3)
but this (4*s+3) in not A; a contradiction.
Therefore the set A has infinitely many primes.

Q.E.D.

Example 3.35
  *TUOLP_03> map prime [2^(2^5)+1, 2^(2^6)+1]
  [False,False]

Exercise 3.36

M_(a*b) := 2^(a*b)-1
        =  2^(a*b) + 2^((a-1)*b) + ... + 2^b
                   - 2^((a-1)*b) - ... - 2^b -1
        =  (2^b-1)*(2^((a-1)*b) + ... + 2^(2*b) + 2^b + 1)

Example 3.37 (Mersenne)
  *TUOLP_03> prime 31
  True
  *TUOLP_03> prime (2^31-1)
  True

Exercise 3.38
Sieve of Eratosthenes

> sieve :: [Integer] -> [Integer]
> sieve (0:ns) = sieve ns
> sieve (n:ns) = n: sieve (mark ns 1 n)
>   where mark :: [Integer] -> Integer -> Integer -> [Integer]
>         mark (y:ys) k m
>           | k == m    = 0:(mark ys 1     m)
>           | otherwise = y:(mark ys (k+1) m)
> primes :: [Integer]
> primes = 2: sieve [3,5..] 

https://wiki.haskell.org/Prime_numbers#Sieve_of_Eratosthenes

Example 3.39
Write a Haskell program to refute the following statement; if
  p_1, ... ,p_k
are all the primes < n, then
  product [p_1 ... p_k] + 1
is a prime.

A computer is a useful tool for refuting guesses or for checking particular cases.

  *TUOLP_03> let example = [take n primes | n <- [0..], not $ prime $ product (take n primes) +1]
  (0.01 secs, 2,055,496 bytes)
  *TUOLP_03> example 
  [[2,3,5,7,11,13],[2,3,5,7,11,13,17],[2,3,5,7,11,13,17,19],[2,3,5,7,11,13,17,19,23],[2,3,5,7,11,13,17,19,23,29]^CInterrupted.

  *TUOLP_03> let mersenne = [(p,2^p-1) | p <- primes, prime (2^p-1)]
  (0.01 secs, 2,100,912 bytes)
  *TUOLP_03> mersenne 
  [(2,3),(3,7),(5,31),(7,127),(13,8191),(17,131071),(19,524287)^CInterrupted.

Check the project called GIMPS as "Great Internet Mersenne Prime Search". 

  *TUOLP_03> let notMersenne = [(p,2^p-1) | p <- primes, not $ prime (2^p-1)]
  (0.01 secs, 2,063,336 bytes)
  *TUOLP_03> notMersenne 
  [(11,2047),(23,8388607),(29,536870911)^CInterrupted.

Example 3.40 (OPEN PROBLEM!)
Are there infinitely many Mersenne primes?

Mersenne primes are related to so-called perfect numbers.
A perfect number is a number n with the sum of all its divisors equals 2*n.
(Or the sum of all proper divisor of n equals n.)
E.g.,
  6 = 1*6 = 2*3 = 3*2 = 6*1
  1+2+3 = 6 

Exercise 3.41 (Euclid)
If 2^n-1 is prime, then 2^(n-1)*(2^n-1) is perfect.

Proof
The proper divisors 2^(n-1)*(2^n-1) are 
  1=2^0,2,2^2, .. ,2^(n-1), 2^n-1, 2*(2^n-1), .. , 2^(n-2)*(2^n-1)
Therefore the sum is
  2^n-1 + (2^n-1)*(2^(n-1)-1) = 2^(n-1)*(2^n-1)

Q.E.D.  

Here is a function for generating the list of proper divisor.
(This is not an efficient way to generate proper divisors.)

> pdivisors :: Integer -> [Integer]
> pdivisors n = [d | d <- [1..(n-1)], n `rem` d == 0]

  *TUOLP_03> pdivisors 8128
  [1,2,4,8,16,32,64,127,254,508,1016,2032,4064]
  *TUOLP_03> sum it
  8128

Prime pairs

> primePairs :: [(Integer,Integer)]
> primePairs = pairs primes
>   where pairs (x:y:xys)
>           | x+2 == y  = (x,y): pairs (y:xys)
>           | otherwise = pairs (y:xys)

  *TUOLP_03> take 50 primePairs 
  [(3,5),(5,7),(11,13),(17,19),(29,31),(41,43),(59,61),(71,73),(101,103),(107,109),(137,139),(149,151),(179,181),(191,193),(197,199),(227,229),(239,241),(269,271),(281,283),(311,313),(347,349),(419,421),(431,433),(461,463),(521,523),(569,571),(599,601),(617,619),(641,643),(659,661),(809,811),(821,823),(827,829),(857,859),(881,883),(1019,1021),(1031,1033),(1049,1051),(1061,1063),(1091,1093),(1151,1153),(1229,1231),(1277,1279),(1289,1291),(1301,1303),(1319,1321),(1427,1429),(1451,1453),(1481,1483),(1487,1489)]

The question
  whether there are infinitely many prime pairs?
is another open problem of mathematics.

Exercise 3.42 (prime triples)
The prime triple is only (3,5,7).

Proof
Let us write the prime triple
  (p, p+2, p+4)
p>1, there only are the following two
  p = 3*q+1 ==> p+2 is NOT a prime
  p = 3*q+2 ==> p+4 is NOT a prime
Thus, only p=1 case holds.

Q.E.D.

Exercise 3.43
Consider the following call:
  
  *TUOLP_03> filter prime [p^2+2 | p<- primes]
  [11^CInterrupted.

It suffices to consider
  p = 3*n
  p = 3*n+1
  p = 3*n+2
In p=3*n case, only p = 3 is a prime.
If p = 3*n+1, then p^2 + 2 becomes
  (3*n+1)^2+2 = 3*(3*n^2 + 2*n + 1)
non a prime.
Similarly,
  (3*n+2)^2+2 = 3*(3*n^2 + 6*n + 2)
is not a prime.
Therefore, p = 3 only satisfies
  p^2+2 :: prime

Q.E.D.
