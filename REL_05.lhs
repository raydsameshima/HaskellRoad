REL_05.lhs

Chapter 05 Relations

> module REL where

> import Data.List
> import SetOrd hiding (unionSet)

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
(N,coprime) : symmetric.

> isCoprime :: Integral a => a -> a -> Bool
> isCoprime m n = (gcd m n == 1)

Note that the (N,coprime) relation is not irreflexive, for 

  *REL> isCoprime 1 1
  True

Definition 5.34
If O is a set of properties of relations on a set A, then the O-closure of a relation R is the smallest relation S that includes R and that has all the properties in O.
That is, R has the properties in O, and for all S that has all the properties in O,
  R \subseteq S.

Exercise 5.35
Suppose that R is a relation on A.
Then R \cup \Delta_A is the reflexive closure and R \cup R^{-1} is the symmetric closure of R.

First, we shall show that 
  R_r := R \cup \Delta_A 
is reflexive.
For arbitrary a \in A, since (a,a) \in \Delta_A,
  a R_r a
holds, i.e., R_r is reflexive.

Next we shall prove R_r is the smallest reflexive relation which includes R.
Suppose S to be an arbitrary reflexive on A and include R:
  R \subseteq S.
Take an arbitrary pair (a,b) \in R_r = R \cup \Delta_A:
  a R_r b.
If a R b, then 
  a S b
holds since R \subseteq S.
Else if a \Delta_A b, i.e., a==b, then the reflexivity of S implies
  a S b==a.
Therefore,
  a R_r b ==> a S b
and  
  R_r \subseteq S.

Similarly, put
  R_s := R \cup R^{-1}.
If (a,b) \in R, then (b,a) \in R^{-1}, and this means R_s is symmetric.

Suppose S to be an arbitrary symmetric relation on A which includes R:
  R \subseteq S.
Then consider an arbitrary pair (a,b) \in R_t, then either
  a R b 
or
  b R a.
Therefore, in either cases, 
  a S b
holds since R \subseteq S.
So
  R_t \subseteq S
and this means R_t is the symmetric closure of R.

Q.E.D.

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

Example 5.37
The sequence of commands
  C1; C2 
is pronounced as execute C1, then C2.
So if the meaning of command C1 is R and C2 is S, then
  C1; C2 ~ S \circ S.

Example 5.38(father of, brother of, and parent of)

Exercise 5.39
Consider the relation
  R := {(0,2), (0,3), (1,0), (1,3), (2,0), (2,3)}
on the set
  A := {0,1,2,3,4}

Then
  R^2 = {(0,0), (0,3), (1,2), (1,3), (2,2), (2,3)}
  R^3 = {(0,2), (0,3), (1,0), (1,3), (2,0), (2,3)}
      = R
  R^4 = R^2

From these results,
  R \cup R^2
is a good candidate for S in
  R \cup (S \circ R) = S.

Q.E.D.

Exercise 5.40
A relation R on A is transitive iff R^2 \subseteq R.

Exercise 5.41(associativity and inverse)

Proposition 5.42
Transitive closure
We will show that for any relation R on A, the relation
  R^+ := \cup_{n \geq 1} R^n
is the transitive closure of R.

Take arbitrary x,y,z in A s.t.
  x R^+ y, y R^+ z,
that is, there are some m,n \in N s.t.
  x R^m y, y R^n z,
and these two conditions implies that
  x R^m \circ R^n z <=> x R^{m+n} z.
Therefore R^+ is transitive:
  x R^+ y, y R^+ z ==> x R^+ z

Next, we shall show that R^+ is the smallest transitive relation which contains R.
Consider an arbitrary trasitive S in A that include R:
  R \subseteq S
For an arbitrary pair in R
  (a,b) \in R <=> a R b,
since we have assumed R \subseteq S,
  a S b.
Assuming n>=1,(a,b) \in R^n, and
  R^n \subseteq S,
then consider 
  (x,y) \in R^{n+1}.
Since
  R^{n+1} = R^n \circ R
and
  x R^{n+1} y :<=> \exists z \in A, (x R^n z, z R y)
Now for this z,
  x S z, z S y
and by the transitivity of S,
  x S y
i.e.,
  R^{n+1} \subseteq S.

Q.E.D.

Example 5.43
If A = {a, {b, {c}}}, then
  a \in^+ A, {b, {c}} \in^+, .. , c \in^+ A.

Example 5.44
  (parents of)^+ = ancestor of
  (child of)^+   = descendant of 

Example 5.45
The relation < on N is the transitive closure of (N, suc):
  suc^+ = <

Exercise 5.46
For a relation R on A, 
  R^+ \cup \Delta_A
is the reflexive transitive closure of R.

Proof
Consider an arbitrary reflexive transitive S which include R:
  R \subseteq S,
and take an arbitrary pair
  (a,b) \in (R^+ \cup \Delta_A)
Then either
  a R^+ b
or
  a==b.
If a R^+ b, then by the result of 4.42,
  (a,b) \in R^+, R \subseteq S ==> R^+ \subseteq S
and since S is also reflexive, i.e.,
  \Delta_A \subseteq S
so R^+ \cup \Delta_A \subseteq S.
Else if b==a, then (a,b==a) \in S, since S is reflexive.

Therefore
  R^+ \cup \Delta_A \subseteq S

Q.E.D.  

Ancestral 
The reflexive transitive closure of a relation R is often called the ancestral of R,
  R^* := R^+ \cup \Delta_A
Note that R^* is a pre order, since R^* is, by definition, is reflexive and transitive.

Exercise 5.47
Give the reflexive transitive closure of
  R := {(n,n+1) | n \in N}
    = suc

  R^* = <= (reflexive and transitive)

Exercise 5.48.1
Show that an intersection of arbitrary many transitive relation is transitive.

Proof
Consider I-indexed R_i \subset A^2 of transitive relations.
To be proved:
  T:=\cap_{i\in I} R_i 
is transitive.

For all
  (x,y),(y,z) \in T,
satisfy for all i\in I,
  x R_i y and y R_i z
Since R_i is transitive, we get for arbitrary i \in I,
  x R_i z.
so
  x T z 
and T is transitive.

Q.E.D.

Exercise 5.48.2
Suppose that R is a relation on A.
(Note that A^2 is a transitive relation on A that extends R.)
Conclude that the intersection of all transitive relations extending R is the least transitive relation extending R.
In other words, R^+ equals the intersection of all transitive relations extending R.
  R^+ = \cap{S | R \subset S \subset A^2, S is transitive}

Proof
For this R, define
  Q:=\cap {S | R \subset S \subset A^2, S is transitive}
then we show that the transitive closure of R is Q: R^+=Q.
Since A^2 is transitive,
  {S| R\subset S \subset A^2, S is transitive}
is not empty, i.e., at least
  A^2 \in {S| R\subset S \subset A^2, S is transitive}.
By definition,
  R \subset Q,
and Q is transitive from 5.48.1, so
  R^+ \subset Q.
Since we have shown in 5.42 that R^+ is the smallest transitive relation which include R, 
  Q = R^+ \cap {S | R \subset S \subset A^2, S is transitive, S \neq R^+}
    = R^+

Q.E.D.

Exercise 5.49.1
  (R^*)^{-1} = (R^{-1})^*
  
Proof
For an arbitrary relation R on a set A,
  R^* := R^+ \cup \Delta_A
  R^+ := \cup_{n >= 1} R^n
and
  (R^*)^{-1} 
  = {(d,c) | (c,d) \in R^+ \cup \Delta_A} 
  = {(d,c) | (c,d) \in R^+} \cup \Delta_A
  = (R^{-1})^*

Q.E.D. 

? Exercise 5.49.2

? Exercise 5.49.3

? Exercise 5.50

5.3 Implementing Relations as Sets of Pairs
Define relations over a type a as sets of pairs:

> type Rel a = Set (a,a)
>
> domR, ranR :: Ord a => Rel a -> Set a
> domR (Set r) = list2set [x | (x,_) <- r]
> ranR (Set r) = list2set [y | (_,y) <- r]

Identity relation over a is

> idR :: Ord a => Set a -> Rel a
> idR (Set xs) = Set [(x,x) | x <- xs]

The total relation is

> totalR :: Set a -> Rel a
> totalR (Set xs) = Set [(x,y) | x <- xs, y <- xs]

Given relation, its inverse is

> invR :: Ord a => Rel a -> Rel a
> invR (Set []) = (Set [])
> invR (Set ((x,y):r)) = insertSet (y,x) (invR (Set r))

...Maybe we can also write this invR with foldr.

  *REL> :t foldr insertSet emptySet
  foldr insertSet emptySet :: (Ord a, Foldable t) => t a -> Set a

> inR :: Ord a => Rel a -> (a,a) -> Bool
> inR r (x,y) = inSet (x,y) r

The complement of a relation:

> complR :: Ord a => Set a -> Rel a -> Rel a
> complR (Set xs) r =
>   Set [(x,y) | x <- xs, y <- xs, not (inR r (x,y))]

A check for reflexivity:

> reflR, irreflR :: Ord a => Set a -> Rel a -> Bool
> reflR set r = subSet (idR set) r
> irreflR (Set xs) r =
>   all (\pair -> not (inR r pair)) [(x,x) | x <- xs]

A check for symmetry:

> symR :: Ord a => Rel a -> Bool
> symR (Set []) = True
> symR (Set ((x,y):pairs))
>   | x == y    = symR (Set pairs)
>   | otherwise = inSet (y,x) (Set pairs)
>                 && symR (deleteSet (y,x) (Set pairs)) 

A check for transitivity:

> transR :: Ord a => Rel a -> Bool
> transR (Set []) = True
> -- transR emptySet = True 
> -- If we put the emptySet, there is an error 
> --   "Pattern match(es) are overlapped"
> transR (Set s) = and [trans pair (Set s) | pair <- s]
>   where
>     trans (x,y) (Set r) = and [inSet (x,v) (Set r) | (u,v) <- r, u==y]

Composition:
Since the composition
  S \circ R := {(a,c) | \exists b aSb and bRc}
we should make a helper function:

> composePair :: Ord a => (a,a) -> Rel a -> Rel a
> composePair (x,y) (Set []) = emptySet
> composePair (x,y) (Set ((u,v):s))
>   | y == u    = insertSet (x,v) (composePair (x,y) (Set s))
>   | otherwise = composePair (x,y) (Set s)

In addition, we need set union.
Note that our set implementation is list without duplicates.
Here is improved version of unionSet (from SetOrd.hs):

> unionSet :: (Ord a) => Set a -> Set a -> Set a
> unionSet (Set []) set2 = set2
> unionSet (Set (x:xs)) set2 =
>   insertSet x (unionSet (Set xs) (deleteSet x set2))

Using above helpers, we can construct the relation composition:

> compR :: Ord a => Rel a -> Rel a -> Rel a
> compR (Set []) _ = emptySet
> compR (Set ((x,y):s)) r =
>   unionSet (composePair (x,y) r) (compR (Set s) r)

Composition of a relation with itself (R^n):

> repeatR :: Ord a => Rel a -> Int -> Rel a
> repeatR r n
>   | n <  1    = error "argument < 1"
>   | n == 1    = r
>   | otherwise = compR r (repeatR r (n-1))

Example 5.51
Let us use the implementation to illustrate Exercise 5.39.

> r = Set [(0,2), (0,3), (1,0), (1,3), (2,0), (2,3)]
> r2 = compR r r
> r3 = repeatR r 3
> r4 = repeatR r 4

Also, the follwoing test yields "True":
  *REL> let s = Set [(0,0), (0,2), (0,3), (1,0), (1,2), (1,3), (2,0), (2,2), (2,3)]
  *REL> (unionSet r (compR s r)) == s
  True

Exercise 5.52
Extend this implementation with a function

> restrictR :: Ord a => Set a -> Rel a -> Rel a

that gives the restriction of a relation to a set.
In the type declaration,
  Set a
is the restricting set.

> restrictR set rel = intersectSet (totalR set) rel
>
> intersectSet :: Ord a => Set a -> Set a -> Set a
> intersectSet (Set []) _ = Set []
> intersectSet (Set (x:xs)) set2
>   | x `inSet` set2 = insertSet x $ intersectSet (Set xs) set2
>   | otherwise      = intersectSet (Set xs) set2
> 

Exercise 5.53
Use 
  unionSet
to define reflexive closure and symmetric closure of a relation.

> rclosR, sclosR :: Ord a => Rel a -> Rel a
> rclosR r = unionSet r (idR background)
>   where 
>     background = unionSet (domR r) (ranR r)
>
> sclosR r = unionSet r (invR r)

Exercise 5.54
Define a function

> tclosR :: Ord a => Rel a -> Rel a

to compute the transitive closure of a relation R, for relations implemented as Ord a => Rel a.

> tclosR r
>   | transR r  = r -- until r becomes transitive.
>   | otherwise = tclosR $ unionSet r (r `compR` r)

That is, until it become transitive, take set-theoretic sum of r:
  r + r^2 + ...

5.4 Implementing Relations as Characteristic Functions

  "x divides y" :<=> \exists q, y = x*q

> divides :: Integral n => n -> n -> Bool
> d `divides` n
>   | d == 0    = error "divides: zero division"
>   | otherwise = (n `rem` d) == 0 

We'll now work out the representation of relations as characteristic functions.

> type Rel' a = a -> a -> Bool
>
> emptyR' :: Rel' a
> emptyR' = \_ _ -> False
>
> list2rel' :: Eq a => [(a,a)] -> Rel' a
> list2rel' xys = \x y -> (x,y) `elem` xys
>
> idR' :: Eq a => [a] -> Rel' a
> idR' xs = \x y -> (x == y) && (x `elem` xs)
>
> invR' :: Rel' a -> Rel' a
> invR' = flip -- :: (a -> b -> c) -> b -> a -> c
>
> -- inR' checks whether a pair in in a relation.
> inR' :: Rel' a -> (a,a) -> Bool
> inR' = uncurry -- :: (a -> b -> c) -> (a, b) -> c
>
> -- isReflective on a list
> reflR' :: [a] -> Rel' a -> Bool
> reflR' xs rel = and [x `rel` x | x <- xs]
>
> irreflR' :: [a] -> Rel' a -> Bool
> irreflR' xs rel = and [not(x `rel` x) | x <- xs]
>
> -- (p ==> q) \equiv (not p || q) \equiv (not (p && not q))
> symR' :: [a] -> Rel' a -> Bool
> symR' xs rel = and [not(x `rel` y && not (y `rel` x)) | x <- xs, y <- xs]
>
> transR' :: [a] -> Rel' a -> Bool
> transR' xs rel
>   = and [ not (x `rel` y && y `rel` z && not (x `rel` z))
>         | x <- xs, y <- xs, z <- xs
>         ]
>
> unionR', intersR':: Rel' a -> Rel' a -> Rel' a
> unionR'  rel1 rel2 x y = x `rel1` y || x `rel2` y
> intersR' rel1 rel2 x y = x `rel1` y && x `rel2` y
>
> reflClosure' :: Eq a => Rel' a -> Rel' a
> reflClosure' rel = unionR' rel (==) -- with "diagonal"
>
> symClosure' :: Rel' a -> Rel' a
> symClosure' rel = unionR' rel (invR' rel)
>
> -- Relation composition on a list.
> compR' :: [a] -> Rel' a -> Rel' a -> Rel' a
> compR' xs rel1 rel2 x y
>   = or [x `rel1` z && z `rel2` y| z <- xs]
>
> -- "Power" of relation, i.e., the composition of a relation with itself.
> repeatR' :: [a] -> Rel' a -> Int -> Rel' a
> repeatR' xs rel n
>   | n <  1    = error "repeatR': the number shold be positive"
>   | n == 1    = rel
>   | otherwise = compR' xs rel (repeatR' xs rel (n-1))

Exercise 5.55

Exercise 5.56

> transClosure' :: [a] -> Rel' a -> Rel' a
> transClosure' xs rel
>   | transR' xs rel = rel
>   | otherwise = transClosure' xs (unionR' rel (compR' xs rel rel))

5.5 Equivalence Relations
Definition 5.57
A relation R on a set A is an equivalence relation iff R is reflexive, transitive, and symmetric.

Example 5.58, 5.59

> -- isEquivalenceRelation
> equivalenceR :: Ord a => Set a -> Rel a -> Bool
> equivalenceR set rel = symR rel && reflR set rel && transR rel
>
> equivalenceR' :: [a] -> Rel' a -> Bool
> equivalenceR' xs rel = symR' xs rel && reflR' xs rel && transR' xs rel

Example 5.60, 5.61, 5.62, 5.63, 5.64

Proposition 5.65 (modulo relation)
  m =_n k :<=> n "divides" (m-k)

Exercise 5.67

> modulo :: Integral n => n -> n -> n -> Bool
> modulo n = \x y -> n `divides` (x-y) 

Example 5.68

> equalSize :: [a] -> [b] -> Bool
> equalSize list1 list2 = (length list1) == (length list2)

Exercise 5.69
1. [(2,3),(3,5),(5,2)]
This is not symmetric, not reflexive, and not transitive since
  (2,3) . (3.5) = (2,5)
is not in it.

2. [(n,m) | |n-m| >= 3]
This is symmetric and reflexive, but not transitive, e.g.,
  (0,3) . (3,6) = (0,6)
is not in it.

Q.E.D.

Exercise 5.70

Exercise 5.71
The number of relations.

If a set A has a finite cardinality n, then
  A^2 has n^2 elements,
  2^(A^2) has 2^(n^2).
On A, all reflexive relation has diagonal elements.
So each non diagonal elements (n*(n-1)) in A^2 determines reflexive relations.
  reflexive: 2^(n*(n-1))
Similarly, the number of elements of symmetric n*n matrix is (n^2+n)/2, so
  symmetric: 2^((n^2+n)/2)

Example 5.72
Assume a relation R on a set A is
  transitive
  reflexive
i.e., R is a preorder on A.
Define
  x ~ y :<=> xRy \and yRx.
Then we will show that this is an equivalence relation.
Symmetry is immediate from the definition.
Since R is reflexive,
  x ~ x :<=> xRx \and xRx <=> xRx
so is ~.
Finally,
  x ~ y \and y ~ z
  :<=> (xRy \and yRx) \and (yRz \and zRy)
Since R is transitive, we get 
  xRz \and zRx :<=> x ~ z.

Q.E.D.

Exercise 5.73
Assume a relation R on A is
  symmetric
  transitive
  \forall x \in A, \exists y \in A s.t. xRy.
Then, we show that R is transitive.
Since R is symmetric,
  yRx
and transitive,
  xRy and yRx ==> xRx,
i.e., R is transitive.

Q.E.D.

Exercise 5.74
Show that R is an equivalence relation iff
  \Delta_A \subseteq R
  R = R \circ R^{-1}

Proof
(==>)
Since R is an equivalence relation, i.e., reflexive, symmetric, and transitive,
  \Delta_A \subseteq R.
For arbitrary (x,y) \in R,
  (x,y) = (x,y) \circ (y,y) \in R \circ R^{-1},
so R \subset R \circ R^{-1}.
Conversely, take an arbitrary (x,y) \circ (y,z) \in R \circ R^{-1}, then since R is symmetric, (y,z) \in R and
  (x,z) = (x,y) \circ (y,z) \in R,
so R \supset R \circ R^{-1} and indeed
  R = R \circ R^{-1}.

(<==)
Suppose R satisfies
  \Delta_A \subseteq R
  R = R \circ R^{-1}
then R is reflexive since for arbitrary (x,y) \in R,
  (x,y) \circ (y,x) \in R \circ R^{-1}
and
  (x,x) \in R.
In addition, for all (x,y) \in R, (y,x) \in R^{-1}, and
  (y,x) = (y,y) \circ (y,x) \in R \circ R^{-1},
that is
  (y,x) \in R
so R is symmetric.
Assume (x,y),(y,z) \in R, then
  (y,x),(z,y) \in R, since R is symmetric
and (y,z) \in R^{-1},
  (x,y) \circ (y,z) \in R \cir R^{-1}
that is
  (x,z) \in R
so R is transitive.

Q.E.D.

5.6 Equivalence Classes and Partitions
Definition 5.75
Suppose R is an equivalence relation on A and a \in A.
The set
  |a| := {b \in A| bRa}
is the R-equivalence class of a, or the equivalence class of a modulo R.

Example 5.76, 5.77

Example 5.78
The equivalence class of 2 in Z (mod 4) is the set {2+4*n| n \in Z}.

  *REL> filter (modulo 4 2) [-15..15]
  [-14,-10,-6,-2,2,6,10,14]

Example 5.79
The equivalence class of 
  {0,1,2}
modulo the equivalence of having the same number of elements is the collection of all three-element sets.

Lemma 5.80
  |a| = |b| <=> aRb

Proof
(==>)
Since the representative element is in its equivalence class,
  a \in |a|
and by the extensionality of sets, 
  a \in |b| = {c|cRb}
Therefore,
  aRb.

(<==)
Since R is symmetric,
  aRb <=> bRa
and for
  |a| = {c|cRa}
we also have
  cRa, aRb ==> cRb
i.e.,
  |a| = {c|cRb} = |b|.

Q.E.D.

Lemma 5.81
Let R be an equivalence relation on A.

1. Every equivalence class is non-empty.
2. Every element of A belongs to some equivalence class.

Since R is reflexive, \forll a \in A,
  aRa
therefore, for arbitrary element a,
  a \in |a|.

3. Different equivalence classes are disjoint.

From the contraposition of 
  |a|=|b| <=> aRb,
we have
  not(aRb) <=> |a| \neq |b|.  

Q.E.D.

Exercise 5.82
Use the implementation 
  Rel' a
as characteristic functions over type a to implement a function

> raccess :: Rel' a -> a -> [a] -> [a]

that takes a relation rel, an object x, and a list lst, and returns the list of all objects f from lst s.t. rel x y holds.

> raccess rel x ys = [y | y <- ys, x `rel` y]

Definition 5.83
A family FA of subsets of a set A is called partition of A iff
  \emptyset \neq FA 
  \cup FA = A
  X,Y \in FA, X \neq Y ==> X \cap Y = \emptyset.

The elements of a partition are called its components.

Example 5.84

Exercise 5.85
If
  {A_i | i \in I}, {B_j | j \in J}
are the partition of A and B, then
  {A_i \times B_j | (i,j} \in I \times J}
is a partition of A \times B.

Proof
Since no i,j with A_i = \emptyset, B_j = \emptyset,
  \emptyset \not\in {A_i \times B_j | (i,j} \in I \times J}
Next,
  \cup_{(i,j) \in I \times J} A_i \times B_j
  = \cup_i A_i \times \cup_j B_j
  = A \times B
Finally, consider
  X,Y \in {A_i \times B_j | (i,j} \in I \times J}
with X \neq Y.
If X \cap Y \neq \emptyset, then we can pick some element
  (a,b) \in X \cap Y
That means
  a \in A_i \cap A_k
  b \in B_j \cap B_l
of some indices.
However, {A_i |i\in I} is the partition of A and 
  A_i \cap A_k = \emptyset
so, we can not pick a, therefore
  X \cap Y = \emptyset.

Q.E.D.

Definition 5.86 (Quotient)
Assume that R is an equivalence on A.
The collection of equivalence classes of R,
  A/R := {|a| | a \in A}
is called the quotient of A modulo R.

Theorem 5.87
Every quotient (of a set, modulo an equivalence) is a partition (of that set).

Proof
From Lemma 5.81.

Q.E.D.

Example 5.88
A/\Delta_A = {{a} | a \in A}
A/(A^2) = {A}

Example 5.89, 5.90, 5.91

Exercise 5.92

Example 5.93 (from Example 5.72)
Let R be a pre-order on A.
Then ~ given by
  x ~ y :<=> xRy \and yRx
is an equivalence relation.
Consider the relation R_~ on A/~ given by
  |x| R_~ |y| :<=> xRy.
The relation R_~ is a partial order on A/~ called the po-set reflection of R.

The definition is independent of the representatives, because assume x~x' and y~y', and xRy.
Then
  xRx' \and x'Rx
  yRy' \and y'Ry
and
  x'Ry' <=> |x'| R_~ |y'|
since R is transitive.

R_~ is reflexive since R is:
  |x| R_~ |x| :<=> xRx.

R_~ is anti-symmetric, for suppose
  |x| R_~ |y|
and
  |y| R_~ |x|
Then 
  xRy \and yRx
and by the definition of ~,
  |x| = |y|

Theorem 5.94
Every partition (of a set) is a quotient (of that set, modulo a certain equivalence relation).

Proof
Let FA be an arbitrary partition of A.
Define
  a~b :<=> \exists S \in FA with a,b \in S
then this is clearly symmetric.
Since FA is a partition, for all a \in A, 
  \exists! S \in FA s.t. a \in S,
and this means
  a~a
and ~ is reflexive.
Assume a~b~c, then there exist S,S' \in FA s.t.
  a,b \in S and b,c \in S'
but since FA is a partition and if S and S' share b then
  S = S'
and
  a,c \in S
that is, S is transitive.
Therefore, S is an equivalence relation determined by the partition FA.

Q.E.D.

Example 5.95, 5.96, 5.97, 5.98, 5.99

Example 5.100
If ~ on 2^N is given by
  A~B :<=> (A-B) \cup (B-A) is finite,
then ~ is reflexive, since (A-A) = \emptyset is finite.

Exercise 5.101
Show that above ~ is an equivalence relation(reflexivity is shown in 5.100).

Proof
Since the left hand side of the definition is symmetric, so is ~:
  A~B :<=> (A-B)\cup (B-A) is finite
      <=>  (B-A)\cup (A-B) is finite
      <=>  B~A

Next, assume
  A~B, B~C
that is
  (A-B)\cup (B-A) is finite
  (B-C)\cup (C-B) is finite
Thus
  ((A-B)\cup (B-A)) \cup ((B-C)\cup (C-B))
is also finite, and is indeed
  (A-C) \cup (C-A) <=>: A~C

Q.E.D.

Here we have used the following lemma.
Let A,B,C be subsets in N, then
  (A-B) \cup (B-C) = A-C.

Since
  A-B := {x\in A| x \not\in B}
  B-C := {y\in B| y \not\in C}
the left hand side becomes
  (A-B) \cup (B-C)
  = {x| (x\in A and not(x\in B)) or (x \in B and not(x\in C))}
  = {x| x\in A and not(x\in C)}
  = A-C

Q.E.D.

Exercise 5.102

Example 5.103, Exercise 5.104

> stirling :: Int -> Int -> Int
> stirling n k
>   | k >  n    = error "bell: first >= second"
>   | k == 1    = 1
>   | n == k    = 1
>   | otherwise = k*(stirling (n-1) k) + (stirling (n-1) (k-1))
>
> bell :: Int -> Int
> bell 0 = 1
> bell n = sum (map (stirling n) [1..n])
>  
> bell' :: Int -> Int
> bell' 0 = 1
> bell' n = sum [stirling n k | k <- [1..n]]
>

Exercise 5.105
  *REL> map bell [0..5]
  [1,1,2,5,15,52]
  *REL> map bell' [0..5]
  [1,1,2,5,15,52] 

Exercise 5.106
Show the second and third conditions 
  \cup FA = F
  X \neq Y \in FA ==> X \cap Y = \empty
in Definition 5.83 of partition are equivalent with
  \forall a \in A, \exists! K \in FA s.t. a \in K.

Proof
(==>)
For all a \in A, there exists some X \in FA s.t. a \in X.
If there exists other Y s.t. a \in Y, then X \cap Y = empty, and it contradicts a \in Y, so there is only one such X.

(<==)
Such K covers A
  \cup K = A,
and its uniqueness implies the disjoint property of third condition.

Q.E.D.

? Exercise 5.107
(R \cap S) of two equivalence relations on A is again an equivalence relation.

? Exercise 5.108

Exercise 5.109 (A list partition)
Consider a list partition xss of a list xs.

> listPartition :: Eq a => [a] -> [[a]] -> Bool

[] is NOT an element of xss,
xs and concat xs have the same elements,
if ys and zs are distinct elements of xss, then ys and zs have no elements in common.

> listPartition xs xss =
>   all (`elem` xs) (concat xss) 
>     && all (`elem` (concat xss)) xs
>     && helper xss []
>     where
>       helper []       _ = True -- base case
>       helper ([]:xss) _ = False -- [] is not in partition
>       helper (xs:xss) dom -- disjointness
>         | xs `intersect` dom == [] = helper xss (xs `union` dom)
>         | otherwise                = False

Exersice 5.110

> listpart2equiv :: Ord a => [a] -> [[a]] -> Rel a
> listpart2equiv dom xss
>   | not (listPartition dom xss) = error "listpart2equiv: argument is not a list partition"
>   | otherwise = list2set $ concat (map f xss)
>   where
>     f xs = [(x,y) | x <- xs, y <- xs]

? Exercise 5.111

Exercise 5.112

> equiv2listpart :: Ord a => Set a -> Rel a -> [[a]]
> equiv2listpart s@(Set xs) r
>   | not (equivalenceR s r) = error "equiv2listpart: argument is not equivalence"
>   | otherwise = genListpart r xs
>   where
>     genListpart r []     = []
>     genListpart r (x:xs) = xclass : genListpart r (xs \\ xclass)
>       where
>         xclass = x : [y|y <- xs, (x,y) `inSet` r]

Exercise 5.113

> equiv2part :: Ord a => Set a -> Rel a -> Set (Set a)
> equiv2part set rel = list2set $ map list2set (equiv2listpart set rel)

Exercise 5.114
For an arbitrary relation R on a set A,
  R_e:= \Delta_A \cup (R \cup R^{-1})^+
is the smallest equivalence relation that includes R.

Proof
Clearly
  R \subset R_e.
R_e is reflexive, because \Delta_A is contained in it.
R_e is symmetric, because all element is either in \Delta_A, or in (R \cup R^{-1}).
R_e is transitive, since R_e is the transitive closure of R.
Therefore, R_e is an equivalence relation which include R.

Assume S is an equivalence relation on A that include R.
Let 
  (c,d) \in R_e
that is either
  d==c
or
  (c,d) \in (R \cup R^{-1})^+
If d==c, then from the reflexivity of S,
  (c,d) \in S,
and R_e \subset S.
Otherwise, there is a k >= 1 with
  (c,d) \in (R \cup R^{-1})^k
Thus, there are (k-1) intermediate elements s.t.,
  c(R\cup R^{-1})r .. r'(R\cup R^{-1})d
Since R \subset S, we also have
  cSr .. r'Sd
and S is transitive,
  cSd
and S is transitive,
  cSd
Therefore R_e \subset S.

Q.E.D.

Exercise 5.115
Let R be a relation on A.
Then 
  S := R^* \cap (R^{-1})^*
is an equivalence relation on A, and the relation T on the quotient A/S given by
  |a|_S T |b|_S :<=> aR^* b
is a partial order.

Proof
Note that
  R^* := R^+ \cup \Delta_A
and
  S := (R^+ \cup \Delta_A) \cap ((R^{-1})^+ \cup \Delta_A)
    =(R^+ \cap (R^{-1})^+) \cup \Delta_A
where we have used the distributive law.

Then S is clearly reflexive and symmetric.
From 5.48, (R^+ \cap (R^{-1})^+) is also transitive, and S is also transitive.
So, S is an equivalence relation, and
  |a|_S := {b \in A | bSa}
is well defined.

Since S is reflexive,
  |a|_S T |a|_S :<=> aR^* a
T is also reflexive.

Assume |a|_S T |b|_S and |b|_S T |a|_S, then by definition,
  aSb and bSa.
This means
  a \in |b|_S and b \in |a|_S 
and 
  |a|_S = |b|_S.
So, T is anti-symmetric.

Since S is transitive, T is also transitive.
Therefore T is a partial order.

Q.E.D.

? Example 5.116

Exercise 5.117, 5.118, 5.119, 5.120

Exercise 5.121 
Prove Theorem 5.94.

? Exercise 5.122

5.7 Integer Partitions
The rule for this game is the followings:
  The first integer partition of n is [n].

  Let B be the last integer partition generated.
  If B consists only of 1's, then done.
  Otherwise, there is a smallest non-1 part m in B.
  To generate the next partition, subtract 1 from m and collect all the units so as to match the new smallest part (m-1).

For example, the partition of 5 starts from
  [5]
The next one is
  [1,4]
and follows
  [1,1,3]
Then, we have [1,1,1,2] as an intermediate partition, but the number of 1's are 3 and is greater than the minimum non-1, i.e., 2, and finally we get
  [1,2,2]
The last two partitions are
  [1,1,1,2]
and
  [1,1,1,1,1]

> type Part = [Int]
> -- Use a compressed form.
> type CmprPart = (Int, Part)
>
> -- From above compressed form to bunch of 1's.
> expand :: CmprPart -> Part
> expand (size,p)
>   | size <= 0 = p
>   | otherwise = 1 : (expand ((size-1),p))
>
> -- The partition that follows
> --   (k, (x:xs))
> -- is generated by packing (k+x, (x:xs)) for maximum size (x-1).
> -- We assume (x:xs) is non-empty, since we use it only in generatePs.
> -- x is the minimum non-1 elements.
> nextPartition :: CmprPart -> CmprPart
> nextPartition (size,(x:xs)) = pack (x-1) ((size+x),xs)
>
> --  
> pack :: Int -> CmprPart -> CmprPart
> pack n c@(size,xs)
>   | n <= 1    = c 
>   | n >  size = pack (n-1) c
>   | otherwise = pack n     (size-n,n:xs)
> --   | otherwise = 
> --       if n > size 
> --       then pack (n-1) (size,xs)
> --       else pack n     (size-n,n:xs)
>
> generatePs :: CmprPart -> [Part]
> generatePs p@(size,[])  = [expand p] -- all 1 case
> generatePs p@(n,(x:xs)) = (expand p) : generatePs (nextPartition p)
>
> part :: Int -> [Part]
> part n
>   | n <  1    = [[]]
>   | n == 1    = [[1]] -- base case
>   | otherwise = generatePs (0,[n])

Exercise 5.123
Write a program

> change :: Int -> [Int]

that returns change in EURO coins for any positive integer, in the least number of coins.

> coinsEU, coinsJP :: [Int]
> coinsEU = [1,2,5,10,20,50,100,200]
> coinsJP = [1,5,10,50,100,500]
>
> change n = moneyBack coinsEU n (n,[]) 
>
> moneyBack coins n (m,xs)
>   | m == 0                   = xs
>   | n <= m && n `elem` coins = moneyBack coins n     (m-n, n:xs)
>   | otherwise                = moneyBack coins (n-1) (m,xs)

  *REL> map change [1..10]
  [[1],[2],[1,2],[2,2],[5],[1,5],[2,5],[1,2,5],[2,2,5],[10]]
  *REL> foldl1 max $ map (length . change) [1..99]
  6
  *REL> foldl1 max $ map (length . change) [1..1000]
  11

> changeJP :: Int -> [Int]
> changeJP n = moneyBack coinsJP n (n,[])
  
  *REL> map changeJP [1..10]
  [[1],[1,1],[1,1,1],[1,1,1,1],[5],[1,5],[1,1,5],[1,1,1,5],[1,1,1,1,5],[10]]

Exercise 5.124
Modify the integer partition algorithm so that it generates all the possible ways of giving coin change for amounts of money up to 10 EURO, using all available EURO(cent) coins
  *REL> coinsEU 
  [1,2,5,10,20,50,100,200]

> packCoins :: Int -> CmprPart -> CmprPart
> packCoins k (m,ks)
>   | k == 1                     = (m,ks)
>   | k <= m && k `elem` coinsEU = packCoins k     (m-k,k:ks)
>   | otherwise                  = packCoins (k-1) (m,ks)
>
> nextCpartition :: CmprPart -> CmprPart
> nextCpartition (k, (x:xs)) = packCoins (x-1) ((k+x),xs)
>
> generateCps :: CmprPart -> [Part]
> generateCps p@(n,[]) = [expand p]
> generateCps p@(n,(x:xs))
>   | x `elem` coinsEU = expand p : generateCps (nextCpartition p)
>   | otherwise = generateCps $ nextCpartition p
>
> partC :: Int -> [Part]
> partC n
>   | n <  1 = [[]]
>   | n == 1 = [[1]]
>   | otherwise = generateCps $ packCoins m (n-m, [m])
>   where
>     m = maxInt $ filter (<= n) coinsEU
>     maxInt []     = 0
>     maxInt (x:xs) = max x (maxInt xs)

Exercise 5.125
  *REL> length $ partC 100
  4563
