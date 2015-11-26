STAL_04.lhs

Chapter 4
Sets, Types and Lists

> module STAL_04 where
> -- import List 
> import DB

4.1 Let's Talk About Sets
There are several axiomatic approaches to set theory; the standard one is due to Zermelo and Frankel.

From wikipedia
1. Axiom of extensionality
2. Axiom of regularity (foundation)
3. Axiom schema of specification (separation, or restricted comprehension)
4. Axiom of pairing
5. Axiom of union
6. Axiom shema of replacement
7. Axiom of infinity
8. Axiom of power set

The follwoing axiom is added to turn ZF into ZFC:
9. Well-ordering theorem

Axioms vs. Theorems, Primitive vs. Defined Notions.

Georg Cantor (1845-1915), the founding father of set theory, gave the follwing description.

The Comprehension Principle.
A set is a collection into a whole of definite, distinct objects of our intuition or or our thought.
The objects are called the elements (member) of the set.

Usually, the objects that are used as elements of a set are not sets themselves.
To handle sets of this kind is unproblematic.
But it is not excluded at all that members are sets.
Thus, in practice, we can encounter sets of sets of ... sets.

Principle of Extensionality.
Sets that have the same elements are equall.
  \forall x (x \in A <=> x \in B) ==> A = B

Subsets.
  \forall x ( x <- A ==> x <- B)

Note that
  A = B <=> (A \subset B && B \subset A)

Theorem 4.1
A \subset A (reflexivity)
A \subset B && B \subset A ==> A = B (antisymmetry)
A \subset B && B \subset C ==> A \subset C (transitivity)

Exersise 4.2
Show that the superset relation also has the properties of Theorem 4.1, i.e., show that \superset is reflexive, antisymmetric and transitive.

Enumeration.
  {a1, ... , an}

Abstraction.
  {x | p x}
denotes the set of things x that have property p.

The abstraction notation binds the variable x:
  {x | p x} = {y | p y}

> naturals = [0..]
> even1 = [n | n <- naturals, even n]
> odds1 = [n | n <- naturals, odd n]
> even2 = [2*n | n <- naturals]

As lists we can "proove" the follwing two are equivalent:

> small_squares1 = [n^2 | n <- [0..999]]
> small_squares2 = [n^2 | n <- naturals, n < 1000]

But Haskell behave differently, small_squares2 won't terminate.

Example 4.5 (The Russel Paradox)
  R := { x | x \nin x}

We do NOT have to be afraid for this kind of paradoxes; if we restrict ourselves to forming sets on the basis of a previously given set:
  { x \in A | p x }

Example 4.6
There is no set corresponding to the properties
  F(x) := there is no infinite sequence
          ... <- x2 <- x1 <- x0 = x

Assume the contrary that F is such a set, and assume F <- F.
This imlies an infinite sequence
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
... there is no general test for checking wheter a given procedure terminates for a particular input.
The halting problem is undecidable.

Collatz problem

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

Suppose halts can be defined, then define the procedure funny

  funny x
    | halts x x = undefined
    | otherwise = True

What about the call funny funny?

