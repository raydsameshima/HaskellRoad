WWN_08.lhs

Working with Numbers

> module WWN_08 where

> import Data.List
> import Nats
> import GHC.Real
> import Data.Complex

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
> myGcd x y -- for negative inputs
>   | x < 0 = myGcd (-x) y
>   | y < 0 = myGcd x (-y)
> myGcd x y 
>   | x == y = x
>   | x <  y = myGcd (y-x) x
>   | otherwise = myGcd y x

Exercise 8.2

> coprime :: Integral a => a -> a -> Bool
> coprime m n = 1 == (gcd m n)

Exercise 8.3

Theorem 8.4
For all positive a,b \in N, there are integers m,n with
  m*a+n*b == gcd a b

Proof
Consider the pairs
  (a,b)=(a0, b0), (a1, b1) .. (ak=bk=GCD(a,b))
generated by Euclid's algorithm.

The initial (a,b) satisfy
  a == 1*a+0*b
  b == 0*a+1*b

Suppose
  ai == m1*a + n1*b
  bi == m2*a + n2*b
If
  ai > bi
then
  a{i+1} == (m1 -m2)*a + (n1-n2)*b
  b{i+1} == m2*a+n2*b 
         == bi
If
  ai < bi
then
  a{i+1} == m1*a + n1*b
         == ai
  b{i+1} == (m2-m1)*a + (n2-n1)*b

Thus every iteration through the loop of Euclid's algorithm preserves the fact that ai and bi are integral linear combinations of
  m*a + nb
of a and b.

This shows that there are integers m,n with
  ak = m*a + n*b
hence that 
  m*a + n*b = gcd a b.

Q.E.D.

Theorem 8.5
If p is a prime that divides a*b, then p divides a or b.

Proof
Suppose p divides a*b but p does not divide a.
Then
  gcd a p == 1
By the previous Theorem 8.4, there are two integer m,n with
  m*a + n*p == 1
Multiplying both sides by b,
  m*a*b + n*p*b == b.
By the fact that p divides a*b, we know that p divides both m*a*b and n*b*p.
Hence p divides m*a*b + n*b*p == b.

Q.E.D.

Theorem 8.6 (Fundamental Theorem of Arithmetic)
Every natural number greater than 1 has a unique prime factorization.

Proof
Theorem 8.5 is the tool for proving this theorem.

In 1.7(The Prime Factorization Algorithm), we have established that every natural number greater than 1 has at least one prime factorization:

> factors n
>   | n <  1 = error "factors: argument should be greater than 1"
>   | n == 1    = []
>   | otherwise = p: factors (n `div` p)
>   where
>     p = leastDiviser n
>     leastDiviser n = ldf 2 n
>     ldf k n
>       | rem n k == 0 = k
>       | k^2 > n      = n
>       | otherwise    = ldf (k+1) n

To show the uniqueness, assume a natural number N(>1) has two different prime factorizations:
  N == p1 * .. * pr
    == q1 * .. * qs
Divide out common factors if necessary.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.


Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.
Since we have assumed they are different factorizations, there at least is one p that is not among the q's.
But this contradicts with the theorem 8.5, because p divides q1 * .. * qs, but p does not divide any of q1, .., qs, since these are all prime numbers different from p.
Thus we have only one prime factorization.

Q.E.D.

8.3 Integers
To make subtraction (the inverse operation of addition) possible between any pair of numbers, we have to introduce negative numbers.
  Z := {0,1,-1,2,-2, .. }
The symbol Z derives from Zahl, the German word for number.

> data Sgn = P | N 
>            deriving (Eq, Show)
> type MyInt = (Sgn, Natural)
>
> myPlus :: MyInt -> MyInt -> MyInt
> (s,m) `myPlus` (t,n)
>   | s == t = (s, m+n)
>   | s == P && n <= m = (P, m-n) -- t == N
>   | s == P && n >  m = (N, n-m) -- t == N
>   | otherwise        = myPlus (t,n) (s,m)

Another implementation is using a difference pair, e.g.,
  (-3) := {(m,n)| m+3==n, m,n \in N}
        = {(0,3),(1,4),(2,5) ..}
Thus we have an equivalence relation R \in N^2:
  (m1,m2) R (n1,n2) :<=> m1+n2 == m2+n1
We write this equivalent class of R as
  [m1-m2] := {(n1,n2) \in N^2 | m1+n2 == m2+n1}
Define addition as a congruence:
  (m1,m2) + (n1,n2) := (m1+n1, m2+n2)
Then
  [m1-m2] + [n1-n2] := [(m1+n1) - (m2+n2)]
  [m1-m2] * [n1-n2] := [(m1*n1+m2*n2) - (m1*n2+n1*m2)]   

Proposition 8.7
For all m,n \in Z, m+n == n+m.

Proof
  [m1-m2] + [n1-n2] == [(m1+n1) - (m2+n2)]
                    == [(n1+m1) - (n2+m2)] \because (+) on N is commutative
                    == [n1-n2] + [m1-m2]

Exercise 8.8
Show that the associativity law for addition holds for the domain of integers.

Proposition 8.9
For all m,n,k \in Z, m*(n+k) == m*n + m*k.

8.4 Implementing Integer Arithmetic

> type NatPair = (Natural, Natural)
>
> plus1, subtr1 :: NatPair -> NatPair -> NatPair
> (m1,m2) `plus1`  (n1,n2) = (m1+n1, m2+n2)
> (m1,m2) `subtr1` (n1,n2) = (m1,m2) `plus1` (n2,n1)
>
> (m1,m2) `mult1` (n1,n2) = (m1*n1+m2*n2, m1*n2+m2*n1)
> -- (m1-m2)*(n1-n2) == m1*m2+m2*n2 - (m2*n1+m1*n2)
>
> eq1 :: NatPair -> NatPair -> Bool
> (m1,m2) `eq1` (n1,n2) = (m1+n2) == (m2+n1)

Here is a reduction toward the canonical representations:

> reduce1 :: NatPair -> NatPair
> reduce1 (m1,Z) = (m1,Z)
> reduce1 (Z,m2) = (Z,m2)
> reduce1 (S m1,S m2) = reduce1 (m1,m2)

Exercise 8.10

> leq1, gt1 :: NatPair -> NatPair -> Bool
> gt1 a b = not $ leq1 b a
> leq1 a b = leq1' (reduce1 a) (reduce1 b)
> leq1' (m,Z) (n,Z) = m >= n

8.5 Rational Numbers
The set of rational numbers (or fractional numbers) can be defined as
  Q := (Z \times Z') / S
where
  Z' := Z - {0}
  (m,n) S (p,q) :<=> m*q == n*p

Proposition 8.11
The law of associativity for (+) holds for the rationals.

Theorem 8.12
Every repeating decimal corresponds to a rational number.

Proof
It suffices to show for the following form
  q := 0.(b1b2 .. bn)(b1b2 .. bn) ..
where
  bi <- [0..9]
Then
  10^n * q - q == (10^n -1)*q
               == b1*10^n + .. + bn
and we can solve it for q:
  q == (b1*10^n + .. bn) `div` (10^n-1)

Q.E.D.

8.6 Implementing Rational Arithmetic
Haskell has a standard implementation of the type Rational:
  data Integral a => Ratio a = a :% a 
                                deriving (Eq)
  type Rational = Ratio Integer

  (%) :: Integral a => a -> a -> Ratio a
  x % y = reduce (x * signum y) (abs y)

  reduce :: Integral a => a -> a -> Ratio a
  reduce x y
    | y == 0    = error "Ratio.%: zero denominator"
    | otherwise = (x `quot` d) :% (y `quot` d)
                  where d = gcd x y

  numerator, denominator :: Integral a => Ratio a -> a
  numerator   (x :% _) = x
  denominator (_ :% y) = y

Note that the numerator of (x % y) need not be equal to x:

  *WWN_08> numerator (5 % 10)
  1
  *WWN_08> denominator (5 % 10)
  2

A total order on the rational is implemented by

  instance Integral a => Ord (Ratio a) where
    compare (x :% y) (x' :% y') = compare (x * y') (x' * y)

The standard numerical operations from the class Num are implemented by
  
  instance Integral a => Num (Ratio a) where
    (x :% y) + (x' :% y') = reduce (x*y' + x'*y) (y*y')
    (x :% y) * (x' :% y') = reduce (x*x') (y*y')
    negate (x :% y)       = negate x :% y
    abs (x :% y)          = abs x :% y
    signum (x :% _)       = signum x :% 1

The rationals are also closed under the division operation
  \x y -> x / y
and the reciprocal operation
  \x -> 1 % x

  instance Integral a => Fractional (Ratio a) where
    (x :% y) / (x' :% y') = (x*y') % (y*x')
    recip (x :% y) = if x < 0 then (-y) :% (-x)
                              else y :% x

> decExpand :: Rational -> [Integer]
> decExpand x
>   | x <  0 = error "decExpand: negatice argument"
>   | r == 0 = [q]
>   | otherwise = q: decExpand ((r*10) % d)
>   where
>     (q,r) = quotRem n d
>     n     = numerator x
>     d     = denominator x

This decExpand can have an infinite output.

Exercise 8.13

8.7 Irrational Numbers

Theorem 8.14
There is no rational number x with x^2==2.

Proof
Assume there is a rational x \in Q with x^2 == 2.
Then there are integers
  x == (m/n), m,n \in Z
with no common factor.

We have
  2 == (m/n)^2
    == m^2/n^2
and
  2*n^2 == m^2.
In other words, m^2 is even, and n^2 is also even.
(Since, if squares of odds are always odds.)
Therefore, there is a integer
  m == 2*m', m' \in Z
and
  2*n^2 == (2*m')^2
        == 4*m'^2
i.e.,
  n^2 == 2*m'^2
which leads to the conclusion that n is also even.

This cotradicts our assumption that m and n has no common factor.

Q.E.D.

Exercise 8.15
Use the method from the proof of Thorem 8.14 to show that \sqrt{3} is irrational.

Exercise 8.16
Show that if p is prime, then \sqrt{p} is irrational.

Exercise 8.17
Show that if n is a natural number with \sqrt{n} not a natural number, then \sqrt{n} is irrational.

Exercise 8.18
Does it follow from the fact that x+y is rational that x is rational or y is rational?
If so, give a proof, if not, give a refutation.

8.8 The Mechanic's Rule
(Also knows as Newton's method.)

> mechanicsRule :: Rational -> Rational -> Rational
> mechanicsRule p x = (1 % 2) * (x + (p * (recip x)))
>
> mechanics :: Rational -> Rational -> [Rational]
> mechanics p x = iterate (mechanicsRule p) x

> sqrtM :: Rational -> [Rational]
> sqrtM p
>   | p <  0    = error "sqrtM: negative argument"
>   | otherwise = mechanics p s
>   where
>     s = if xs == [] then 1 
>                     else last xs
>     xs = takeWhile (\m -> m^2 <= p) [1..]

Exercise 8.19

Exercise 8.20

8.9 Reasoning about Reals

Lemma
The composition of two continuous functions is continuous.

Proof
Let f:X\to A, and g:A \to B be continuous, i.e.,
  \forall x, \forall e > 0, \exists d > 0, \forall y,
    (|x-y| < d ==> |f(x)-f(y)| < e)

  \forall a, \forall e' > 0, \exists d' > 0, \forall b,
    (|a-b| < d' ==> |g(a)-g(b)| < e')

Consider g.f : X\to B, take
  e == d'
then
  (|x-y| < d ==> |f(x)-f(y)| < e==d')
If we identify (a==f(x), b==f(y)), then
  (|f(x)-f(y)| < d'==e ==> |g(f(x))-g(f(y))| < e')
Therefore, we have \forall x, \forall e' > 0, \exists d > 0, \forall y,
  (|x-y| < d ==> |g.f(x)-g.f(y)| < e')
i.e., g.f is also continuous.

Q.E.D.

Limits
Let
  a: N \to R
be a real sequence, and a' \in R.
The expression
  \lim_{i\to\infty} a_i = a'
by definition means that
  \forall e>0 \exists n \forall i >= n (|a'-a_i|<e)

Theorem
Every sequence of reals has at most one limit.

Proof
Let b,b' be two different limit of a: N \to R.
Now
  \forall e>0, \exists n,n' \forall i>=n, j>=n'
    (|b-a_i| < e)
    (|b'-a_j| < e)
Therefore, pick
  m := max n n'
we have
  \forall e>0, \exists m \forall i,j >= m
    (|b-a_i| < e)
    (|b'-a_j| < e)
Using the triangle inequality,
  |b-b'| == |b-a_i-(b'-a_i)|
         == |b-a_i+a_i-b'|
         <= |b-a_i| + |b'-a_i|
         <  e + e
Since the choice of e>0 is arbitrary, and this means
  |b-b'| == 0.

Q.E.D.

Exercise 8.21

Exercise 8.22
Assume that
  \lim_{i\to\infty} a_i == a
then
  \lim_{i\to\infty} a_{2*i} == a
and if f:N\to N is a function s.t.
  \forall n \exists m \forall i >= m (f(i)>=n),
then
  \lim_{i\to\infty} a_{f(i)} == a.

Proof
Since
  \forall e>0, \exists n \forall i>=n (|a_i - a| < e)
Now for this i,
  2*i > i >= n
and
  (|a_{2*i} - a| < e
This means
  \lim_{i\to\\infty} a_{2*i} == a.

Next, let e>0 be arbitrary, and n0 s.t.
  \forall j >= n0, (|a-a_j| < e)
For this n0, we have m0 s.t.
  \forall i >= m0, (f(i) >= n0)
and
  (|a_a_{f(i)}| < e)
Therefor 
  \lim_{i\to\infty} a_{f(i)} == a.

Q.E.D.

Exercise 8.23
Assume that the sequances of reals 
  {a_n}_n, {b_n}_n
have lmits a resp. b, and that
  a < b.
Show that a number n exists s.t. \forall m >= n(a_m < b_m).

Proof
For an arbitrary e>0, there is na, nb s.t.
  \forall i >= na, |a_n - a| < e
  \forall i >= nb, |b_n - b| < e
So take
  n = max na nb
and
  \forall i >= n, (|a_n - a| < e \land |b_n - b| < e).

Take
  e0 := (b-a)/3
and there is n s.t.
  \forall i >= n, (|a_n - a| < e0 \land |b_n - b| < e0).
i.e.,
  a-e0 < a_n < a+e0
and
  b-e0 < b_n < b+e0
Then
  b_n - a_n >  b-e0 - (a+e0)
            == (b-a) - 2*e0
            == (b-a)/3
            >  0

Q.E.D.

Exercise 8.24
Assume
  lim_{i\to \infty} a_i == a, \lim_{i\to \infty} b_i == b
then
  lim_{i\to \infty} (a_i+b_i) == a + b

Proof
Since \forall e>0, there is na, nb with
  \forall i >= na, |a_i - a| < e
  \forall i >= nb, |b_i - b| < e
Take 
  n := max na nb
and
  |a_i+b_i - (a+b)| == |a_i - a + b_i - b|
                    <= |a_i - a| + |b_i - b|
                    <  2*e

Q.E.D.

Exercise 8.25(epsilon-delta v.s. sequence continuous)
Show that a function
  f:R \to R
is continuous iff
  \lim_{i\to \infty} a_i = a ==> \lim_{i\to \infty} f(a_i) == f(a)
  
Proof
(==>)
Suppose f:R \to R is (epsilon-delta)continuous, i.e., \forall x \in R,
  \forall e>0, \exists d>0, \forall y (|x-y|<d ==> |f(x)-f(y)|<e)
Then, for all sequence {a_n}_n that converge to a:
  \forall e'>0, \exists n s.t. \forall i >= n,
  |a_i - a| < e'
take
  e' < d
and
  |a_i - a| < e'(<d) ==> |f(a_i)-f(a)| < e
this means (sequence-continuous)
  \lim_{i\to\infty} f(a_i) == f(a).

(<==)
Suppose f:R\to R satisfies
  \lim_{i\to \infty} a_i = a ==> \lim_{i\to \infty} f(a_i) == f(a)
That is f is (sequence)conticuous; if
  \forall e>0, \exists n s.t. \forall i >= n, |a_i - a| < e
then
  \forall e'>0, \exists n' s.t. \forall j >= n',|f(a_j) - f(a)| < e'
So, for this e>0, if we take
  m := max n n'
we have
  \forall i >= m, |a_i-a|<e ==> \forall j >= m, |f(a_j)-f(a)|<e
that is for an arbitrary e>0, choose a_k (k >= max i j) and
  |a_k-a| < e ==> |f(a_k)-f(a)| < e
So f is (epsilon-delta)continuous.

Q.E.D.  

Therefore, for this e>0, take
  m := max n n'  
Now for arbitrary i >= m, 
  d := |a_i - a|

Cauchy
A sequence of reals {a_n}_n is called Cauchy iff
  \forall e>0 \exists n \forall i,j >= n (|a_i - a_j|<e)

Exercise 8.26
Assume that the sequence {a_n}_n is Cauchy.

1.
Show that the sequence is bounded, i.e., there are numbers b and c s.t.
  \forall i (b < a_i < c).

2.
Assume that a\in R is s.t. \forall e>0 \forall n \exists i>=n(|a-a_i|<e).
(The existence of such an a follows from the sequence being bounded, but you are not asked to prove this.)
Show that \lim_{i\to\infty}a_i == a.

Proof
1.
Consider an arbitrary e>0, then 
  \exists n \forall i,j >= n (|a_i - a_j|<e).
Let
  b := min (a_0, ..., a_n) - e
We will show that b < a_i: for i \in [1..n] by definition,
  b < a_i, i \in [1..n]
For i>n, if a_n < a_i, then again b<a_i is immediate from the definition:
  b < a_n < a_i (i>n).
If a_n > a_i, then since
  |a_n - a_i| < e
and
  a_n - a_i < e <=> a_n - e < a_i
but by definition
  b <= a_n - e < a_i ==> b < a_i.
Therefore we have
  b < a_n, \forall n

Analogously, for an arbitrary e>0, we can prove
  a_n < c,
where 
  c := max (a_0, ..., a_n) + e.

2.
Let e>0 be arbitrary.
Since {a_n}_n is Cauchy, we have n1 s.t.,
  \forall i,j>=n1(|a_i-a_j|<e).
From the assumption, there is k>=n1 s.t.
  |a-a_k|<e
Then \forall i >= k (>=n1),
  (|a_k-a_i| < e),
so \forall i >= k,
  (|a-a_k|<e \land |a_k-a_i|<e)
From the triangle inequality, \forall i,
  |a-a_i| <= |a-a_k| + |a_k-a_i|
          <  e + e == 2*e
This means \lim_{i\to\infty}a_i == a.

Q.E.D.

It follows immediately from Exercise 8.19 that the sequence of rationals produced by the Mechanic's rule are Cauchy.
Thanks to that we can implement a program for calculating square roots as follows:

> approximate :: Rational -> [Rational] -> Rational
> approximate epsilon (x:y:zs)
>   | abs (y-x) < epsilon = y
>   | otherwise           = approximate epsilon (y:zs)
>
> apprx :: [Rational] -> Rational
> apprx = approximate (1/10^6)
>
> mySqrt :: Rational -> Rational
> mySqrt = apprx . sqrtM

Exercise 8.27
Just as we defined the integers from the naturals and the rationals from the integers by means of quotient sets generated from suitable equivalence classes, we can do so now, by defining the set of real numbers R as the set of all Cauchy sequences in Q modulo an appropriate equivalence relation.
Define that equivalence relation and show that it is indeed an equivalence relation.

Define a relation for Cauchy sequences as
  {a_n}_n ~ {b_n}_n :<=> {a_n-b_n}_n \to 0
then, this relation is reflexive:
  {a_n - a_n}_n == {0}_n
symmetric:
  {a_n-b_n}_n \to 0 <=> {b_n-a_n}_n \to 0
and transitive:
  a_n - c_n == a_n - b_n + b_n - c_n
            \to 0 + 0 == 0
Therefore, this relation is an equivalence relation.

Q.E.D.

8.10 Complex Numbers

Exercise 8.28
Check that the commutative and associative laws and the distributive law hold for C.

There is a standard Haskell module with an implementation of complex numbers:

  *WWN_08 Data.Complex> :info (:+)
  data Complex a = !a :+ !a   -- Defined in ‘Data.Complex’
  infix 6 :+

The exclamation marks in the typing indicate that both the real and imaginary parts of type Complex are evaluated in a strict way.

Exercise 8.29

Exercise 8.30(De Moirvre's formula)

