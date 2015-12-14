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



