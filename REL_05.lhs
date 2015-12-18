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
where R is a relation, we usually write
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

> properDivs :: Integer -> [Integer]
> properDivs n = init (divs n)

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

Example 5.16, 5.17 (irreflexive relations)

Symmetric
A relation R on A is symmetric if for all a,b \in A, aRb ==> bRa.

Example 5.18 (having the same age)






