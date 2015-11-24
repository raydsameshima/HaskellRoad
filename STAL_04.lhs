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
