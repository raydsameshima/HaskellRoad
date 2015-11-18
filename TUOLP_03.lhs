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
'(prime) of prime' is for later convinience.

> prime :: Integer -> Bool
> prime n 
>   | n < 0     = error "not a posive"
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


