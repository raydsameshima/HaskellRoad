REL_05.lhs

Chapter 05 Relations

> module REL where

> import Data.List
> import SetOrd

5.1 The Notion of a Relation

Definition 5.1 (Relation, Domain, Range = Codomain)
A relation is a set of ordered pairs.
Instead of 
  (x,y) \in R
where R is a relation, we usually write it as
  xRy.

The set
  dom(R) = {x | \exists y (xRy)}
is called the domain of R, and
  cod(R) = {y | \exists x (xRy)} = ran(R)
is called the codomain or range. 

Example 5.2
If A and B are sets, then
  A \times B
and
  \emptyset
are relations, especially \emptyset is called trivial relation.
    
E.g.
  dom(\emptyset) = \emptyset = cod(\emptyset)
if B \neq \emptyset, then
  dom(A \times B) = A
  (dom(A \times \emptyset) = dom(\emptyset) = \emptyset)
and if A \neq \emptyset, then
  cod(A \times B) = B

Definition 5.3 (From ... to, between, on)
The relation R is a relation from A to B, or between A and B, if 
  dom(R) \subset A
and
  cod(R) \subset B.

A relation from A to A is called on A.

If R is a relation on A, then A is called the underlying set (of the structure that consists of the domain A and the relation R).

Example 5.4

Example 5.5
If A is a set, then \subset is a relation on 2^A.

Example 5.6 (>=, <= on R)

Definition 5.7 (Identity and Inverse)
1.
  1_A := {(a,b) \in A^2 | a==b} 
       = {(a,a) | a \in A}
is a relation on A, the identity on A.

2. If R is a relation between A and B, then
  R^{-1} := {(b,a) | aRb }
the inverse of R, is a relation between B and A.

Example 5.8 ("child of")

Example 5.9
1. A \times B is the "biggest" relation from A to B.
2. \emptyset is the "smallest" relation from A to B.
3. For the usual ordering < of <^{-1} = >.
4. (R^{-1})^{-1} = R, (1_A)^{-1} = 1_A, \emptyset^{-1} = \emptyset, and (A \times B)^{-1} = B \times A.

Example 5.10
If R is the set of pairs
  (n,m)
where both n and m are integer, s.t.
  n^2 is a divisor of m
the definition of R may look as follows:
  \forall n,m \in Z, nRm :<=> n^2|m.

In Haskell,
 
> example_5_10 = \n m -> rem m n^2 == 0

Example 5.11 (divisor)
For all n \in N, the set ot pairs
  {(a,b) | a,b \in N, ab = n, a <= b}
is a relation on N.
This relation gives all the divisor pairs of n.

> divisors :: Integer -> [(Integer, Integer)]
> divisors n = [ (d, quot n d) | d <- [1..k], rem n d == 0]
>   where k = floor . sqrt . fromInteger $ n
  
  *REL> divisors (2^11-1)
  [(1,2047),(23,89)]
  *REL> divisors (2^13-1)
  [(1,8191)]

  *REL> 11 `quot` 2
  5
  *REL> map (`quot` 2) [8..15]
  [4,4,5,5,6,6,7,7]

Example 5.12

> isPrime'' :: Integer -> Bool
> isPrime'' = \n -> divisors n == [(1,n)]
  
  *REL> zip [1..] (map isPrime'' [1..12])
  [(1,True),(2,True),(3,True),(4,False),(5,True),(6,False),(7,True),(8,False),(9,False),(10,False),(11,True),(12,False)]

Also, here are the list of divisors of a natural number, the list of all proper divisors of a natural number, and a test for being a perfect natural number:

> divs :: Integer -> [Integer]
> divs n = (fst list) ++ reverse (snd list)
>   where list = unzip (divisors n)

> divs' :: Integer -> [Integer]
> divs' n = smaller ++ larger
>   where 
>     (smaller, rLarger) = unzip (divisors n)
>     larger = reverse rLarger

> properDivs :: Integer -> [Integer]
> properDivs n = init (divs' n)

> perfect :: Integer -> Bool
> perfect n = sum (properDivs n) == n

where

  *REL> :type init
  init :: [a] -> [a]
  *REL> init "aiueo"
  "aiue"

  *REL> divs 6
  [1,2,3,6]
  *REL> divs 12
  [1,2,3,4,6,12]
  *REL> properDivs 6
  [1,2,3]
  *REL> properDivs 12
  [1,2,3,4,6]
  *REL> perfect 12
  False
  *REL> perfect 6
  True
  
  *REL> filter perfect [1..100000]
  [1,6,28,496,8128]

Exercise 5.13
Show that 
  \forall x \forall y \exists R (xRy)

Proof
Take
  R := {(x,y)}
of a singleton.

Q.E.D.

5.2 Properties of Relations
Reflexive
A relation R is reflexive on A if \forall a \in A, aRa.

Example 5.14
On any set A, the relation 1_A is reflexive, and 1_A is the "smallest" reflexive relation on A: it is a subset of any reflexive relation on A.
In other words, a relation R is reflexive on A iff 1_A \subset R.

Example 5.15
The relation <= on N is reflexive (for every natural number is less than or equal to itself).

Irreflexive
A relation R on A is irreflexive if for no x \in A, xRx.

Example 5.16 (irreflexive relations)
E.q., (N, <) is irreflexive.

Example 5.17 (irreflexive relations)
A relation IR is irreflexive iff \Delta_A \cap IR = \emptyset.

Symmetric
A relation R on A is symmetric if for all a,b \in A, aRb ==> bRa.
That is
  (\forall a,b \in A, aRb ==> bRa) ==> R is symmetric 

Example 5.18 (having the same age)

Exercise 5.19
1. A relation R on a set A is symmetric iff
  \forall x,y \in A (xRy <=> yRx)
2. A relation R is symmetric iff 
  R \subseteq R^{-1},
3. iff
  R = R^{-1}

Proof
1. 
(==>) part is trivial. 
(<==) part; if
  \forall x,y \in A (xRy <=> yRx)
then xRy and yRx, i.e., R is symmetric.

2.
(==>) part; if R is symmetric, 
  aRb ==> bRa
this means
  if (a,b) \in R then (b,a) \in R
and
  (a,b) \in R ==> (b,a) \in R <=> (a,b) \in R^{-1}
Thus 
  \forall (a,b) \in R ==> (a,b) \in R^{-1}
and
  R \subseteq R^{-1}
(<==) part; if R = R^{-1}, then
  aRb <=> bRa
and this shows R is symmetric.

3. Similar to 2.

Q.E.D.

Asymmetric
A relation R on A is asymmetric if for all x,y \in A, if xRy then not yRx:
  xRy ==> not yRx.

(<,N) is asymmetric.
Immediately from the definition, a relation R on A is asymmetric iff
  R \cap R^{-1} = \emptyset
Note that there are relations which are neither symmetric nor asymmetric.

Exercise 5.20
Show that every asymmetric relation is irreflexive.

Proof
If R is asymmetric, 
  xRy ==> not yRx
this can be applied for the case of y==x, and then
  xRx ==> not xRx
i.e., R is not reflexive.

Q.E.D.

Antisymmetric
A relation R on A is antisymmetric if for all x,y \in A, if xRy and yRx then x==y:
  xRy and yRx ==> x==y.

Example 5.21
The relation m|n (m is a divisor of n) on N is antisymmetric.
If m is a divisor of n and n is a divisor of m, then m and n are equal.

The relation (<=,N) in example 5.15 is antisymmetric.
  n <= m <= n ==> m==n

Example 5.22
Show from the definitions that an asymmetric relation R
  xRy ==> not yRx
always is antisymmetric
  xRy and yRx ==> x==y.

Proof
If R is asymmetric, we have
  xRy ==> not yRx.
Thus, if we assume x /= y, then
  (xRy and yRx) ==> (not xRy) and (not yRx)
holds but this contradicts the if statement: (xRy and yRx).
Therefore we have x == y.

Q.E.D.

Transitive
A relation R on A is transitive if for all x,y,z \in A:
  if xRy and yRz then xRz.

? Exercise 5.23
Show that R on A is transitive iff
  \forall x,z \in A (\exists y \in A (xRy \land yRz) ==> xRz)

Proof

Example 5.24

Pre-order (or quasi-order)
R on A is a pre-order (or quasi-order) if R is transitive and reflexive:
  xRy, yRz ==> xRz
  xRx

? Example 5.25 (\vDash)
Let L be the set of all propositional formulas built from a given set of atomic propositions.
Then the relation \vDash given by
  P \vDash Q iff P ==> Q is logically valid
is a pre-order on L.

To check this, note that for every propositional formula P,
  P ==> P
is logically valid, so \vDash is reflexive.

? Example 5.26

Strict partial order
A relation R on A is a strict partial order if R is transitive and irreflexive.
  xRy, yRz ==> xRz
  no x \in A, xRx

Partial order
A relation R on A is a partial order if R is transitive, reflexive and antisymmetric:
  xRy, yRz ==> xRz
  xRx
  xRy, yRx ==> x==y

Example 5.27 (N, <) and (2^A, \subset)

Exercise 5.28
Show that every strict partial order is asymmetric.

Proof
An strict partial order is transitive and irreflexive.
An irreflexive R satisfies
  no x \in A, xRx.
If x,y \in A satify
  xRy and yRx,
then from the transitive property, 
  x==y
but it contradicts irreflexive property.
So
  not (xRy and yRx) \equive (not xRy) or (not yRx),
i.e., R is asymmetric.

Q.E.D.

Exercise 5.29
Show that every relation which is transitive and asymmetric is a strict partial order.

Proof
An asymmetric R satisfies
  xRy ==> not yRx
Therefore, if there were x \in A satisfies xRx, then
  xRx ==> not xRx
holds, and it clearly contradicts.
Thus 
  no x \in A, xRx,
i.e., R is irreflexive, and a strict partial order.

Q.E.D.

Exercise 5.30
If R is a strict partial order on A, then
  R \cup \Delta_A
is a partial order on A.

Exercise 5.31
Show that the inverse of a partial order is again a partial order.

Proof
For an arbitrary partial order R,
  R = {(x,y) | xRy}
with
  xRy and yRz ==> xRz
  xRx
  xRy and yRx ==> x==y
Thus, the inverse
  S := R^{-1} 
     = {(y,x) | xRy}
satisfies
  ySx and zSy <=> zSy and ySx 
              ==> zSx
  xSx
  ySx and xSy ==> y==x
so, S = R^{-1} is also a partial order.

Q.E.D.

Linear (or total) order, chain
A relation R on A is linear if for all x,y \in A is "comparable":
  xRy, yRx or x==y.

All Haskell type in class 
  Ord a
are total orders.

A set A with a total order on it is called a chain.

Exercise 5.32 (Trees)
Let S be a reflexive (xSx) and symmetric (xRy ==> yRx) relation on A.
A path is a finite sequence
  a_1 S a_2 S ... S a_n

Assume that for all a,b \in A, there exists a unique path connecting a with b.

Fix r \in A, and define
  a<=b iff a is one of elements in the path connecting r with b.

This <= is reflexive(a<=a), since there is a trivial path (on A)
  aSa. 

This <= is antisymmetric, since if a<=b and b<=a, i.e.,
  r S .. S a S .. S a_i S .. S b and r S .. b S .. S b_j S .. S a 
there are some sequences {a_i} and {b_j} from r.
The uniqueness implies these two sequence are identical and 
  a==b.

This <= is transitive, since if a<=b<=c, then we have a sequence
  r S .. S a S .. S b S .. S c
That is,
  a<=c.

For all a \in A, r <= a, since we have assumed there is a unique path between any two elements in A, so
  r S .. S .. S a <=> r <= a.

For all a \in A, the set
  X_a = {x \in A | x <= a}
is finite and if b,c \in X_a then b <= c or c <= b.
Since there is a unique path
  r S .. S a.
So the set X_a is determined by the unique path
  X_a = {a_i | .. S a_i S .. S a}
If this unique path is infinite, it contradicts the uniqueness of the paths.Therefore this set is
  X_a = {a_i | a_n S .. S a_i S .. S a}
Thus for all b,c \in X_a, either
  b S .. S c
or
  c S .. S b
is the sub path of X_a.

Q.E.D.

Exercise 5.33
(N,<) : irreflexive, asymmetric, transitive, linear.
(N,<=) : reflexive, antisymmetric, transitive, linear.
(N,successor) : irreflexive, asymmetric, intransitive.
(N,divisor) : reflexive, antisymmetric, transitive.
(N,coprime) : irreflexive, symmetric, 

> isCoprime :: Integral a => a -> a -> Bool
> isCoprime m n = (gcd m n == 1)

Definition 5.34
If O is a set of properties of relations on a set A, then the O-closure of a relation R is the smallest relation S that includes R and that has all the properties in O.
That is, R has the properties in O, and for all S that has all the properties in O,
  R \subseteq S.

Exercise 5.36
Let R be a transitive binary relation on A.
Does it follow from the transitivity of R that its symmetric reflexive closure
  S := R \cup R^{-1} \cup \Delta_A
is also transitive?

It does NOT.
Consider 
  A := {1,2,3}
  R := {(1,2), (1,3)}
then R is transitive, but its symmetric reflexive closure is
  S := {(1,2), (1,3), (2,1), (3,1), (1,1), (2,2), (3,3)}
So, (2,1) and (1,3) are in S, but (2,3) is not.
That is, even if R is transitive, the symmetric reflexive closure may not be transitive.

Q.E.D.



