IAR_07.lhs

Induction and Recursion

> module IAR_07 where

> import Data.List
> import STAL_04 (display)

7.1 Mathematical Induction
1. Basis (Base case)
Prove that 0 has the property P.
  P(0)
2. Induction step
Assume the induction hypothesis that n has property P.
Prove on the basis of this that n+1 has property P.
  P(n) ==> P(n+1)

The goal
  \forall n \in N, P(n)
follows from this by the principle of mathematical induction:

Fact 7.1
For every set
  X \subset N
we have that
  0 \in X and \forall n \in N(n\in X) ==> n+1 \in X) ==> X=N.

Example 7.2 Sum of the Angles of a Convex Polygon.
The angle of a convex polygon of (n+3) sides is (n+1)*\pi radians.

Proof
Base case
For n=0, it holds, since any triangle has \pi as the sum of the angles.

Induction step
Assume the sum of the angles of a convex polygon of (n+3) sides is (n+1)*\pi radians.
Consider a convex polygon P of (n+4) sides.
Connecting 1st and 3rd edges, we can decompose P into a polygon P' of (n+3) sides and a triangle T'.
The sum of the angles of P equals the sum of P' and T':
  (n+1)*\pi + \pi = (n+1+1)*\pi

From the principle of mathematical induction, the statement follows.

Q.E.D.

Example 7.3
The sum of the first n odd numbers.

\sum_{k=1}^n (2*k-1) = n^2

> sumOdds, sumOdds' :: Integer -> Integer
> sumOdds' n = sum [2*k-1 | k<-[1..n]]
> sumOdds  n = n^2

  *IAR_07> and (map (\n -> sumOdds' n == sumOdds n) [1..1000])
  True

Example 7.4
The sum of the first n even numbers.

\sum_{k=1}^n 2*k = n*(n+1)

> sumEvens, sumEvens' :: Integer -> Integer
> sumEvens' n = sum [2*k | k<-[1..n]]
> sumEvens  n = n*(n+1)

> sumInts n = sumEvens n `div` 2

Example 7.5, Exercise 7.6
Summing squares.

\sum_{k=1}^n k^2 = n*(n+1)*(2*n+1)/6

> sumSquares, sumSquares' :: Integer -> Integer
> sumSquares' n = sum [k^2 | k<-[1..n]]
> sumSquares  n = n*(n+1)*(2*n +1) `div` 6

Example 7.7, Exercise 7.8
Summing cubes.

\sum_{k=1}^n = (n*(n+1)/2)^2

> sumCubes, sumCubes' :: Integer -> Integer
> sumCubes' n = sum [k^3 | k<-[1..n]]
> sumCubes  n = (n*(n+1) `div` 2)^2

Exercise 7.9
Prove that for all n \in N, 3^(2*n+3) + 2^n is divisible by 7.

Proof
Base case (n=0)
3^3 + 1 = 28 = 7*4

Induction step
Let us assume 
  3^(2*n+3)+2^n = 7*k, k\in N
Then
  3^(2*(n+1)+3)+2^(n+1)
   = 3^(2*n+3+2)+2^(n+1)
   = 9*3^(2*n+3)+2*2^n
   = 9*(7*k -2^n) +2*2^n
   = 9*7*k + (2-9)*2^n
   = 7*(9*k-2^n)
Therefore, from the principle of mathematical induction, the statement holds.

Q.E.D.

Remark(well-founded)
For any A that is well-founded by a relation < the following principle holds.
Let X \subset A, if
  \forall a \in A(\forall b < a(b\in X) ==> a \in X),
then X=A.

7.2 Recursion over the Natural Numbers

> data Natural = Zero
>              | Succ Natural
>              deriving (Eq, Show)

The recursive definition of addition on the natural numbers.
1. m+0     := m
2. m+(n+1) := (m+n)+1

> plus :: Natural -> Natural -> Natural
> m `plus` Zero = m
> m `plus` (Succ n) = Succ (m `plus` n) 

We can prove the following list of fundamental laws of addition:
  m+0     = m       (0 as the additive identity element)
  m+n     = n+m     (commutativity)
  m+(n+k) = (m+n)+k (associativity)

Proposition 7.10
\forall m,n,k \in N,
  m+(n+k) = (m+n)+k (associativity)

Proof
We prove it induction on k.

Base case
  m+(n+0) = m+n     (+.1.)
          = (m+n)+0 (+.1.)

Induction step
Assume
  m+(n+k) = (m+n)+k
then
  m+(n+(k+1)) = m+((n+k)+1) (+.2.)
              = (m+(n+k))+1 (+.2.)
              = ((m+n)+k)+1 (i.h.)
              = (m+n)+(k+1) (+.2.)
Therefore, from the principle of mathematical induction, the statement holds.

Q.E.D.

Proposition 7.11
\forall m,n \in N,
  m+n = n+m (commutativity)

Proof
We prove it induction on n.

Base case (n=0)
Induction on m.
  Base case (m=0)
    0+0 = 0 = 0+0

  Indunction step
  Let us assume 
    m+0 = 0+m
  then
    (m+1)+0 = m+1 (+.1.)
            = (m+0)+1 (+.1.)
            = (0+m)+1 (i.h.)
            = 0+(m+1) (associativity) 
  So \forall m \in N,
    m+0 = 0+m.

Induction step
Assume
  m+n = n+m
then
  m+(n+1) = (m+n)+1 (+.2.)
          = (n+m)+1 (i.h.)
          = n+(m+1) (+.2.)
          = n+(1+m) (i.h.)
          = (n+1)+m (associativity)
Therefore, commutativity for addition on natural numbers holds.

Q.E.D.

Once we have addition, we can define multiplication:
1. m*0     := 0
2. m*(n+1) := (m*n)+m    

> mult :: Natural -> Natural -> Natural
> m `mult` Zero = Zero
> m `mult` (Succ n) = (m `mult` n) `plus` m

> natural2Int :: Natural -> Int
> natural2Int Zero = 0
> natural2Int nat = helper nat 0
>   where helper Zero n = n
>         helper (Succ m) n = helper m (n+1)

  *IAR_07> Succ (Succ Zero) `mult` Succ (Succ (Succ Zero))
  Succ (Succ (Succ (Succ (Succ (Succ Zero)))))
  *IAR_07> natural2Int it
  6

The operation for exponentiation on naturals is also recursive:

> expn m Zero = (Succ Zero) 
> expn m (Succ n) = (expn m n) `mult` m

  *IAR_07> expn (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))
  Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))
  *IAR_07> natural2Int it
  8

Exercise 7.13
Prove by mathematical induction that
  k^(m+n) = k^m*k^n

Proof
Induction on n.
Base case (n=0)
  k^(m+0) = k^m
          = k^m * 1
          = k^m * k^0
Induction step
Let us assume
  k^(m+n) = k^m*k^n
then
  k^(m+(n+1)) = k^((m+n)+1)
              = k^(m+n) * k
              = k^m * k^m * k
              = k^m * k^(m+1)
Therefore, the statement holds.               

Q.E.D.

We can define the relation <= on N as follows
  m <= n :<=> \exists k \in N, m+k=n.
We use
  m < n
for
  m <= n \land m \neq n

> leq Zero     _        = True
> leq (Succ _) Zero     = False
> leq (Succ m) (Succ n) = leq m n

> geq m n = leq n m
> gt m n = not $ leq m n
> lt m n = gt n m

Exercise 7.14 (cut-off subtraction)

> subtrN :: Natural -> Natural -> Natural
> subtrN Zero _    = Zero
> subtrN m    Zero = m
> subtrN (Succ m) (Succ n) = subtrN m n

Exercise 7.15 (quotient and remainder on naturals)

> quotientN, remainderN :: Natural -> Natural -> Natural
> quotientN _ Zero = error "quotientN: zero-division"
> quotientN m n
>   | gt n m    = m
>   | otherwise = quotientN (m `subtrN` n) n
> 
> remainderN m n = m `subtrN` m'
>   where
>     m' = (quotientN m n) `mult` m

7.3 The Nature of Recursive Definitions
The format:
  f(0)   := c
  f(n+1) := h(f(n))

The general procedure is easily implemented in an operation foldn, defined as follows:

> foldn :: (a -> a) -> a -> Natural -> a
> foldn h c Zero     = c
> foldn h c (Succ n) = h (foldn h c n)

> exclaim :: Natural -> String
> exclaim = foldn ('!':) []

> plus' = foldn (\n -> Succ n)
> mult' m = foldn (plus' m) Zero
> expn' m = foldn (mult' m) (Succ Zero)

Exercise 7.16

> subtr' = foldn pre
>
> pre :: Natural -> Natural
> pre Zero     = Zero
> pre (Succ n) = n

Exercise 7.17 (Fibonacci)
For all n > 1,
  F_{n+1} * F_{n-1} - (F_n)^2 = (-1)^n.

Proof
Base case (n=2)
  F_3 * F_1 - (F_2)^2 = 2*1 - 1^2 = 1 = (-1)^2

Induction step
Assume 
  F_{n+1} * F_{n-1} - (F_n)^2 = (-1)^n
then
  F_{n+2} * F_n - (F_{n+1})^2 
   = (F_n+F_{n+1})*F_n - (F_{n+1})^2
   = (F_n)^2 - F_{n+1}*(F_{n+1}-F_n)
   = (F_n)^2 - F_{n+1}*F_{n-1}
   = -(-1)^n
   = (-1)^{n+1}
Therefore, from the principle of mathematical induction, the statement follows.

Q.E.D.

Exercise 7.18
A bitlist is a list of zeros and ones.
Consider the following code bittest for selecting the bitlist without consecutive zeros.

> bittest :: [Int] -> Bool
> bittest []       = True
> bittest [0]      = True
> bittest (1:xs)   = bittest xs
> bittest (0:1:xs) = bittest xs
> bittest _        = False

1.
How many bitlists of length 0(1,2,3) satisfy bittest?

2.
Let a_n be the number of bitlists of length n without consecutive zeros.
Give an induction proof to show that for every n >= 0 it holds that
  a_n = F_{n+2},
where F_n is the n-th Fibonacci number.

length 0 : []
length 1 : [0], [1]
length 2 : [1,0], [1,1], [0,1]
length 3 : [0,1,0], [0,1,1], [1,0,1], [1,1,0], [1,1,1]

So the list of a_n is
  [1,2,3,5, ..

For length = 0,1,
  a_0 = 1 = F_2
  a_1 = 2 = F_3
In general, a_n is given by
  a_n = a_{n-1} -- (0:xs) 
      + a_{n-2} -- (0:1:xs)
Since the initial conditions are the same as Fibonacci, we have
  a_n = F_{n+2}

Q.E.D.

Exercise 7.19
Show that the following two implementations are the same.

> fib 0 = 0
> fib 1 = 1
> fib n = fib (n-1) + fib (n-2)

> fib' n = fib2 0 1 n
>   where
>     fib2 a _ 0 = a
>     fib2 a b n = fib2 b (a+b) (n-1)

Base case
  *IAR_07> fib' 0
  0
  *IAR_07> fib' 1
  1

Induction step
Now
  fib2 (fib i) (fib (i+1)) n
   = fib2 (fib (i+1)) (fib i + fib (i+1)) (n-1)
   = fib2 (fib (i+1) (fib (i+2)) (n-1)
   = fib2 (fib (i+2) (fib (i+3)) (n-2)
   = ...
   = fib2 (fib (i+n)) (fib (i+n+1)) 0
   = fib (i+n)
holds for arbitrary i,n \in N.

So 
  fib' n = fib2 0 1 n
         = fib2 (fib 0) (fib 1) n
         = fib (0+n)
         = fib n

Q.E.D.


