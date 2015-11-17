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
> primes = 2: filter prime [3,5..]

Theorem 3.33 (Euclid)
There are infinitely many prime numbers.

Exercise 3.34
Show that
  A := [4*n + 3| n<-[0..]]
contains infinitely many primes.

Proof
Let us assume there are only finitely many primes in A:
  A = [p(1),p(2)... p(n)| p(i) = 4*n(i) + 3]
Consider
  N := 4*p(1)* ... *p(n) -1
    =  4*(p(1)* ... *p(n) -1) + 3
Clearly N is an odd number.
If N is prime, we have a contradiction.
Otherwise N has a prime factor q, different from all p's.
  N = q * N'
Now, q has the form either
  4*r + 1 or 4*r + 3,
since q>2 is an odd prime.
If q = 4*r + 3 then done, so it suffices to consider q = 4*r + 1 form.

