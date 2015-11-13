TAMO_02.lhs

2. Talking about Mathematical Objects

> module TAMO_02 where

2.1 Logical Connectives and their Meanings
Every statement that makes mathematical sense is either True or False.

The idea behind this is that (according to the adherents) the world of mathematics exists independently of the mind of the mathematician.
Solving problems in a mathematics textbook is like visiting famous places with a tourist guide.

This belief in an independent world of mathematical fact is called 
  Platonism, 
after the Greek philosopher Plato, who even claimed that our everyday physical world is somehow an image of this ideal mathematical world.

Not every working mathematician agrees with the statement that the world of mathematics exists independently of the mind of the mathematical discover.
The Dutch mathematician Brouwer (1881-1966) and his followers have argued instead that the mathematical reality has no independent existence, but is created by the working mathematician.
According to Brouwer the foundation of mathematics is in the intuition of the mathematical intellect.
A mathematical
  Intuitionist
will therefore not accept certain proof rules of classical mathematics, such as proof by contradiction, as this relies squarely on Platonist assumptions.

Connectives
and:             conjunction
or:              disjunction
not:             negation
if, then:        implication
if, and only if: equivalence

Remark
Do not confuse (if, then) on one hand with (thus), (so), (therefore) on the other.
The difference is that the phrase (if, then) is used to construct conditional statements, while (thus), (so), (therefore) are used to combine statements into pieces of mathematical reasoning (or: mathematical proofs).
We will never write (=>) when we want to conclude from one mathematical statement to the next.
The rules of inference, the notion of mathematical proof, and the proper use of the word (thus) are the subject of Chapter 3.

Iff = if, and only if

Negation
not :: Bool -> Bool

Conjunction
(&&) :: Bool -> Bool -> Bool

Disjunction
inclusive v.s. exelusive

Remember
\lor is always inclusive or.

Example 2.1
For all integer x, x<1 or 0<x.
... True

(||) :: Bool -> Bool -> Bool

Exercise 2.2
Make up the truth table for the exclusive version of or.

> xor :: Bool -> Bool -> Bool
> xor True False = True
> xor False True = True
> xor _     _    = False

Implication
P ==> Q := if P(antecedent), then Q(consequent).

> infix 1 ==>
> (==>) :: Bool -> Bool -> Bool
> x ==> y = (not x) || y

or explicitly
  True  ==> x = x
  False ==> x = True

Trivially True Implications
E.g. the empty set \emptyset = {} is included in every set.

Remark:"trivial"

Implication and Causality

Converse and Contraposition
The converse of an implication P ==> Q is Q ==> P; its contraposition is not Q ==> not P.

Necessary and Sufficient Conditions
sufficient ==> necessary

Equivalence
P <=> Q := P ==> Q && Q ==> P

> infix 1 <=>
> (<=>) :: Bool -> Bool -> Bool
> x <=> y = x == y

Example 2.3
P => Q is the only if part, and P <= Q is if part.

Exercise 2.4
Check the equivalence of or (P `xor` Q) and (not (P <=> Q)).

> infix 2 <+>
> (<+>) :: Bool -> Bool -> Bool
> x <+> y = x /= y

Consider the following formula:

> p,q :: Bool
> p = True
> q = False

> formula1 :: Bool
> formula1 = (not p) && (p ==> q) <=> not (q && (not p))

  *TAMO_02> formula1 
  False

2.2 Logical Validity and Related Notions
Logical Validities
There are popositional formulas that receive the calue True no matter what the values of the occuring letters.
Such formlas are called logically valid, e.g.
  P ==> P, P || not P, P ==> (Q ==> P)

Truth Table of an expression.

Example 2.5(Establishing Logical Validity by Means of a Truth Table)

> formula2 :: Bool -> Bool -> Bool
> formula2 p q = ((not p) && (p ==> q) <=> not (q && (not p)))

formula2 is a propositional function or Boolean function.

Here is the case for propositions with one proposition letter (type Bool -> Bool).

> valid1 :: (Bool -> Bool) -> Bool
> valid1 bf = (bf True) && (bf False) 

The validity check for Boolean functions of type 
  bf :: Bool -> Bool
is suited to test functions of just one variable.
An example is the principle of excluded middle:

> excluded_middle :: Bool -> Bool
> excluded_middle p = p || not p

  *TAMO_02> valid1 excluded_middle 
  True

> valid2 :: (Bool -> Bool -> Bool) -> Bool
> valid2 bf = (bf True True) && (bf True False)
>          && (bf False True) && (bf False False)

> form1, form2 :: Bool -> Bool -> Bool
> form1 p q = p ==> (q ==> p)
> form2 p q = (p ==> q) ==> p

  *TAMO_02> valid2 form1
  True
  *TAMO_02> valid2 form2
  False

Using the list comprehension, we can make valid3 and valid4:

> valid3 :: (Bool -> Bool -> Bool -> Bool) -> Bool
> valid3 bf = and [ bf p q r | p <- [True, False], 
>                              q <- [True, False], 
>                              r <- [True, False]]
> valid4 :: (Bool -> Bool -> Bool -> Bool -> Bool) -> Bool
> valid4 bf = and [ bf p q r s | p <- [True, False], 
>                                q <- [True, False], 
>                                r <- [True, False],
>                                s <- [True, False]]

Leaving out Parentheses
(&&) and (||) bind more strongly than (==>) and (<=>).
Thus,
  p && q ==> r = (p && q) ==> r

Operator Precedence in Haskell
In Haskell, the convention is not quite the same.
Therefore, we should use parenthesis.

Logically Equivalent
Two formulas are called (logically) equivalent if, no matter the truth values of the letters P,Q, ... occuring in these formulas, the truth values obtained for them are the same.
This can be checked by constructing a truth table.

The same concepts of the equallity of functions:
  f,g :: a -> b, f=g :<=> forall x <- a, f(a) = g(a).

Example 2.6 (The First Law of De Morgan)
  not (p && q) \equiv (not p || not q)

Example 2.7(De Morgan Again)
  not (p || q) \equiv (not p && not q)

Example 2.8
A pixel on a computer screen.

Exercise 2.9

> ex_2_9 :: Bool -> Bool -> Bool
> ex_2_9 p q  = (((p `xor` q) `xor` q) <=> p)
  
  *TAMO_02> valid2 ex_2_9 
  True

In Haskell, logical equivalence can be tested as follows.

> logEquiv1 :: (Bool -> Bool) -> (Bool -> Bool) -> Bool
> logEquiv1 bf1 bf2 = (bf1 True <=> bf2 True)
>                  && (bf1 False <=> bf2 False)

> logEquiv2 :: (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> Bool
> logEquiv2 bf1 bf2 =
>    and [(bf1 p q) <=> (bf2 p q) | p <- [True, False], 
>                                   q <- [True, False]]

> logEquiv3 :: (Bool -> Bool -> Bool -> Bool) -> 
>   (Bool -> Bool -> Bool -> Bool) -> Bool
> logEquiv3 bf1 bf2 =
>    and [(bf1 p q r) <=> (bf2 p q r) | p <- [True, False], 
>                                       q <- [True, False], 
>                                       r <- [True, False]]

Let's redo Exercise 2.9:

> formula3 p q = p
> formula4 p q = (p <+> q) <+> q
  
  *TAMO_02> logEquiv2 formula3 formula4
  True

> formula5 p q = p <=> ((p <+> q) <+> q)

  *TAMO_02> valid2 formula5
  True

Warning
Don't confuse \equiv and <=>(iff).
If \Phi and \Psi are formulas, then 
  \Phi \equiv \Psi 
expresses the statement that both statements are equivalent.
On the other hand, 
  \Phi <=> \Psi 
is just another formula.
See Exercise 2.18.

Theorem 2.10, 2.11

> test1 = (\p -> p) `logEquiv1` \p -> not (not p)
> test2a = (\p -> p && p) `logEquiv1` id
> test2b = (\p -> p || p) `logEquiv1` id
> test3 = (\p q -> p ==> q) `logEquiv2` (\p q -> ((not p) || q))
> test4 = (\p q -> (not p) ==> (not q)) `logEquiv2` (\p q -> q ==> p)
> test5 = (\p q -> p <=> q) `logEquiv2` (\p q -> (p ==> q) && (q ==> p))
> test6 = (\p q -> p && q) `logEquiv2` (\p q -> q && p)
> test7 = (\p q -> not (p && q)) `logEquiv2` (\p q -> (not p) || (not q))
> test8 = (\p q r -> p && (q && r)) `logEquiv3` (\p q r -> (p && q) && r)
> test9 = (\p q r -> p && (q || r)) `logEquiv3` (\p q r -> (p && q) || (p && r))

Theorem 2 12
  *TAMO_02> (\p -> p ==> False) `logEquiv1` (\p -> (not p))
  True
  *TAMO_02> (\p -> p || False) `logEquiv1` id
  True

Substitution Principle:
Just a dummy.

Example 2.14
p := not p

Exercise 2.15
A propositional contradiction is a formula that yields false for every combination of truth values for its proposition letters.

> isContradiction1 :: (Bool -> Bool) -> Bool
> isContradiction1 bf = not $ and [bf x | x <- [True,False]] 
  
  *TAMO_02> isContradiction1 (\p -> False)
  True

Exercise 2.16
Produce useful denial for every sentence of Exercise 2.31, i.e. for every formula \Phi, the denial of it is (not \Phi).

Exercise 2.17
  x < y < z \equiv x<y && y<z
Therefore its denial is
  x=>x || y=>z

Exercise 2.18
Show:
  (\Psi <=> \Phi) \equiv (not \Phi <=> not \Psi) 

Proof
Think about the truth table of the formula (\Psi <=> \Phi).
Taking not flip True and False, but does not change (not \Phi <=> not \Psi).

Q.E.D.

Exercise 2.19
Show that
  \Psi \equiv \Phi
is true iff \Psi <=> \Phi is logically valid.

Proof
==> part:
\Psi \equiv \Phi means that for arbitrary input, they will return the same Boolean values, and then \Psi <=> \Phi is always True.

<== part:
If \Psi <=> \Phi = True, they are the same Boolean function, i.e. \Psi \equiv \Phi.

Q.E.D.

Exercise 2.20
1.
  *TAMO_02> let f = \p q -> (not p ==> q)
  *TAMO_02> let g = \p q -> (p ==> not q)
  *TAMO_02> f `logEquiv2` g
  False

2.
  *TAMO_02> let f = \p q -> (not p ==> q)
  *TAMO_02> let g = \p q -> (q ==> not p)
  *TAMO_02> f `logEquiv2` g
  False

4.
  *TAMO_02> let i = \p q r -> p ==> (q ==> r)
  *TAMO_02> let j = \p q r -> q ==> (p ==> r)
  *TAMO_02> i `logEquiv3` j
  True

6.
  *TAMO_02> let f = \p q -> (p ==> q) ==> p
  *TAMO_02> let g = \p q -> p
  *TAMO_02> f `logEquiv2` g
  True

7,
  *TAMO_02> let f = \p q r -> (p || q) ==> r
  *TAMO_02> let g = \p q r -> (p ==> r) && (q ==> r)
  *TAMO_02> f `logEquiv3` g
  True

Exercise 2.21

2.3 Making Symbolic Form Explicit

Exercise 2.22
\forall r<s \in Q, \exists t \in Q s.t.
  r < t < s,
since just take
  t := (r + s)/2.

Quantifiers
\forall, \exists

Exercise 2.23 (structure trees)

Example 2.24, 2.25 (restrictions)

Exercise 2.26, 2,27

Bound Variables.
Quantifier expressions like
  \forall x, \exists y \in R, etc
are said to bind every occurance of x,y,etc in their scope.
If a variable occurs bound in a certain expression then the meaning of that expression does not change when all bound occurences of that variable are replaced by another one. (alpha equivalence of lambda calculus)

