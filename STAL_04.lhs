STAL_04.lhs

Chapter 4
Sets, Types and Lists

> module STAL_04 where
> import Data.List 
> import DB

4.1 Let's Talk About Sets
There are several axiomatic approaches to set theory; the standard one is due to Zermelo and Frankel.

From Wikipedia
1. Axiom of extensionality
2. Axiom of regularity (foundation)
3. Axiom schema of specification (separation, or restricted comprehension)
4. Axiom of pairing
5. Axiom of union
6. Axiom schema of replacement
7. Axiom of infinity
8. Axiom of power set

The following axiom is added to turn ZF into ZFC:
9. Well-ordering theorem

Axioms vs. Theorems, Primitive vs. Defined Notions.

Georg Cantor (1845-1915), the founding father of set theory, gave the following description.

The Comprehension Principle.
A set is a collection into a whole of definite, distinct objects of our intuition or or our thought.
The objects are called the elements (member) of the set.

Usually, the objects that are used as elements of a set are not sets themselves.
To handle sets of this kind is unproblematic.
But it is not excluded at all that members are sets.
Thus, in practice, we can encounter sets of sets of ... sets.

Principle of Extensionality.
Sets that have the same elements are equal.
  \forall x (x \in A <=> x \in B) ==> A = B

Subsets.
  \forall x ( x <- A ==> x <- B)

Note that
  A = B <=> (A \subset B && B \subset A)

Theorem 4.1
A \subset A (reflexivity)
A \subset B && B \subset A ==> A = B (antisymmetry)
A \subset B && B \subset C ==> A \subset C (transitivity)

Exercise 4.2
Show that the superset relation also has the properties of Theorem 4.1, i.e., show that \superset is reflexive, antisymmetric and transitive.

Enumeration.
  {a1, ... , an}

Abstraction.
  {x | p x}
denotes the set of things x that have property p:
  a \in {x | p x} \equive p a \equive p a = True

The abstraction notation binds the variable x:
  {x | p x} = {y | p y}

> naturals = [0..]
> even1 = [n | n <- naturals, even n]
> odds1 = [n | n <- naturals, odd n]
> even2 = [2*n | n <- naturals]

As lists we can "prove" the following two are equivalent:

> small_squares1 = [n^2 | n <- [0..999]] -- restriction: see page 121
> small_squares2 = [n^2 | n <- naturals, n < 1000]

But Haskell behave differently, small_squares2 won't terminate.
The 1st pattern, small_squares1 is good, because it restrict its "universe" and therefore it will terminate.

Example 4.5 (The Russel Paradox)
  R := { x | x \nin x}

We do NOT have to be afraid for this kind of paradoxes; if we restrict ourselves to forming sets on the basis of a previously given set:
  { x \in A | p x }

Example 4.6
There is no set corresponding to the properties
  F(x) := there is no infinite sequence
          ... <- x2 <- x1 <- x0 = x

Proof
Assume the contrary that F is such a set, and assume F <- F.
This implies an infinite sequence
  ... F <- F <- F <- F
So by the defining property of F, F \nin F.

Assume F \nin F, then by the defining property of F, there is an infinite
sequence
  ... x2 <- x1 <- x0 = F.
Now take a subsequence of this infinite sequence 
  ... x2 <- x1
By the defining property of F,
  x1 \nin F,
contradicting
  F = x0 -> x1.

Q.E.D.

Exercise 4.7
Assume that A is a set of sets.
Show that 
  { x <- A | x \nin x } \nin A.

Proof
Let B be the set
  B := { x <- A | x \nin x }
and
  B <- A.
Suppose B <- B, then from the definition of B, B \nin B, contradiction.
Suppose B \nin B, then from the definition of B, B <- B, contradiction.
Therefore such B \nin A.

Q.E.D.
  
It follows from Exercise 4.7 that every set A has a subset
  B \subset A
with
  B \nin A,
taking
  B := { x <- A | x \nin x }

4.2 Paradoxes, Types and Type Classes
... there is no general test for checking whether a given procedure terminates for a particular input.
The halting problem is undecidable.

Collatz problem (sequence)

> run :: Integer -> [Integer]
> run n
>   | n < 1 = error "give me positive argument"
>   | n == 1 = [1] -- termination condition
>   | even n = n : run (div n 2) -- Integer is not an instance of (/)
>   | odd  n = n : run (3*n + 1)

Haskell has no way to distinguish between divergence and error abortion.

Russel type paradox
We say that a procedure diverges when it does not terminate or when it aborts with an error.
Stipulating divergence in Haskell is done by means of the predeclared function undefined, which causes an error abortion, just like error.
In fact, Haskell has no way to distinguish between divergence and error abortion.

"The halting problem is undecidable."

Proof
Suppose halts can be defined, then define the procedure funny

  funny x
    | halts x x = undefined
    | otherwise = True

What about the call funny funny?

Suppose funny funny does not halt, then by definition, we are in the first case, because second case does halt.
But the argument is now funny funny, and therefore funny funny should halt, but contradiction.

Suppose funny funny halts, then by definition, we are in the second case.
However, if funny funny halts, we should be in the first case, then funny funny does not halt, and contradiction.

Thus, there is something wrong with the definition of funny.
The only peculiarity of definition is the use of the halts predicate.
This shows that such halts predicate cannot be implemented.

Q.E.D.

It should be clear that funny is a rather close analogue to the Russell set
  {x | x \nin x}.
Such paradoxical definitions are avoided in functional programming by keeping track of the types of all objects and operations.

How does type discipline avoid the halting paradox?

Consider the definition of funny:
  funny x
    | halts x x = undefined
    | otherwise = True
It makes a call to halts.
What is the type of halts?
The procedure halts takes as first argument a procedure, say proc, and as second argument to that procedure, say arg.
This means that
  proc :: a -> b
  arg :: a
and
  proc arg :: b
but this means that the application 
  halts x x
is the definition of funny is ill-formed, for as we have seen the types of the two arguments to halts must be different, so the arguments themselves must be different.

Another example (elem)
In order to be able to identify things, they should be instances of Eq.
Haskell operations denotes computation procedures, and there is no principled way to check whether two procedures perform the same task.

Exercise 4.8

4.3 Special Sets
Singletons.
  {a}

Remark.
Whether the equation
  a = {a}
has solutions is answered differently by different axiomatizations of set theory.

> ones = 1:ones

A set of the form
  {a,b}
is called an unordered pair.
Of course, if a=b, then
  {a,b} = {a}
is, in fact, a singleton.

Empty Set.
  {} or \emptyset

Note that there is exactly one set that is empty: this is due to Extensionality:
Let {},{}' be different empty sets, but by Extensionality,
  {} = {}'
since they have no elements.

Theorem 4.9
For every set A, we have that
  {} \in A.

Proof
Since
  \forall x(x \in {} ==> x \in A)
is true, because {} has no element.
Thus
  {} \in A
holds.

Q.E.D.

Exercise 4.10, 4.11

Remark. Abstraction and Restricted Quantification.
Note that
  \forall x \in A \Phi(x) = True <=> {x\in A| Phi(x)} = A.
Similarly,
  \exists x \in A Phi(x) = True <=> {x\in A | Phi(x)} \neq {}.

4.4 Algebra of Sets
Definition 4.12 (Intersection, Union, Difference.)
Assume that A and B are sets.
1. A \cap B = {x | x<-A && x<-B} 
2. A \cup B = {x | x<-A || x<-B}
3. A - B    = {x | x<-A && not(x <- B)}

Types of Set Theoretic Expressions
&&, || and \cap, \cup has different "type".

Exercise 4.13
What are the types of the set difference operator - and of the inclusion operator?
  (-) :: Set s => s -> s -> s
  (\subset) :: s -> s -> Bool

Exercise 4.14 

The relationships become clearer if we write
1. x<-A \cap B <=> x<-A && x<-B}
2. x<-A \cup B <=> x<-A || x<-B
3. x<-A - B    <=> x<-A && not(x <- B)

Disjointness.
Sets A anb B are called disjoint if
  A \cap B = {}

Example 4.15

Theorem 4.16 
Theorem 4.17
Example 4.18
Exercise 4.19

Complement.
Fix a set X (as a universe), of which all sets to be considered are subsists.
The complement is given by
  A^c := X - A
Clearly, we have that for all x<-X,
  x <- A^c <=> x \nin A

Theorem 4.20

Symmetric Difference.
A \oplus B := {x|x\in A \xor x\in B}

Exercise 4.21

Definition 4.22 (Power Set)
The powerset of the set X is
  2^X := {A|A\subset X}

Exercise 4.23
(\subset, 2^X) has the properties of reflexivity, antisymmetry and transitivity, like (<=, R).
The relation <= on R has linearity;
  \forall x,y \in R, x<=y or y<=x.
Show that 2^X lacks this property.
(E.g., take X:={0,1}, then clearly {0},{1} \subset X, but we have no inclusion relation between {0},{1}.)

Definition 4.24 (Generalized Union and Intersection)

A set of sets is sometimes called a family of sets or a collection of sets.
(Of course we can NOT take "a set of all sets", but we can take a class or all sets.)

Example 4.25

Example 4.26
Let F and G be collections of sets.
The translation of 
  \cup F \subset \cap G
becomes
  \forall x (\exists X(X \in F && x \in X)) ==> \forall Y(Y \in G ==> x \in Y)
Similarly, the translation of
  \cap F \subset \cup G
becomes
  \forall x(\forall X(X \in F ==> x \in X)) ==> \exists Y(Y \in G && x \in Y)

Types of Generalized Union and Intersection
Their type is
  {s} -> s,

Exercise 4.27
Let F be a family of sets.
Show that there is a set A with the following properties:
  1. F \subset 2^A,
  2. \forall sets B, if F \subset 2^B, then A \subset B.

Proof.
Take A:=2^(\cup F), then
  \forall X(X \in F ==> X \subset \cup F)
  <=> \forall X(X \in F ==> X \in 2^(\cup F))
  <=> F \subset 2^(\cup F)
and

 

Example.28

Exercise 4.29 (Theorem 4.20)

Exercise 4.30

Exercise 4.31

