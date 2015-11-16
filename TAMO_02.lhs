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
We will never write (==>) when we want to conclude from one mathematical statement to the next.
The rules of inference, the notion of mathematical proof, and the proper use of the word (thus) are the subject of Chapter 3.

iff = if, and only if

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

Or explicitly
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
P ==> Q is the only if part, and P <== Q is if part.

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
There are propositional formulas that receive the value True no matter what the values of the occurring letters.
Such formulas are called logically valid, e.g.
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

The same concepts of the equality of functions:
  f,g :: a -> b, f=g :<=> \forall x <- a, f(a) = g(a).

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
  x>=x || y>=z

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
are said to bind every occurrence of x,y,etc in their scope.
If a variable occurs bound in a certain expression then the meaning of that expression does not change when all bound occurrence of that variable are replaced by another one. (alpha equivalence of lambda calculus, or "dummy")

Example 2.28 (dummy)

Example 2.29 (Summation, Integration)
  *TAMO_02> sum [i | i<- [1..5]]
  15
  *TAMO_02> sum [j | j<- [1..5]]
  15

Example 2.30 (Abstraction)
  [x|x<- lst, p x] = [y|y<- lst, p y]

Translation Problems.
Exercise 2.31, 2.32, 2.33

Expressing Uniqueness.
\exists! x :<=> \exists x (p x && \forall z, (p z ==> z = x)).

Exercise 2.34, 2.35, 2.36

Remark.
Expanding the definitions of mathematical concepts is not always a good idea.
E.g.
  "n is prime" :<=> n>1 && \exists d s.t. (1<d<n && d|n),
where (m|n) for "m divides n".

Before we'll start looking at the language of mathematics and its conventions in a more systematic way, we'll make the link between mathematical definitions and implementations of those definitions.

2.4 Lambda Abstraction

> square1, square2 :: Integer -> Integer
> square1 x = x^2
> square2   = \x -> x^2

> m1, m2 :: Integer -> Integer -> Integer
> m1 = \x -> \y -> x*y
> m2 = \x y -> x*y

The solution formula of quadratic equations:
  a*x^2 + b*x + c = 0, a \= 0.

> solveQdr :: (Float, Float, Float) -> (Float, Float)
> solveQdr = \(a,b,c) ->
>   if a == 0 then error "not quadratic, give me non zero a!"
>             else let d = b^2 - 4*a*c 
>                  in  if d<0 then error "no real solutions"
>                             else ((-b-sqrt d)/(2*a), (-b+sqrt d)/(2*a))

2.5 Definitions and Implementations
A natural number n is prime if n>1 and no number m with 1<m<n divides n:
  n>1 && not \exists m (1<m<n && m|n).
Another way of expressing this is the following:
  n>1 && \forall m ((1<m<n) ==> not m|n).

Let's define a formula:
  isPrime n :\equiv n>1 && \forall m ((1<m<n) ==> not m|n)..
One way to think about this definition is as a procedure for testing whether a natural number is prime.
The implementation of ld(n) function in chapter 1 is
  isPrime n :\equiv n>1 && \forall m ((1<m && m^2 <= n) ==> not m|n)
            :\equiv n>1 && ld(n) = n.

2.6 Abstract Formulas and Concrete Structures

Open Formulas, Free Variables, and Satisfaction.
An occurrence of a variable in an expression that is not (any more) in the scope of a quantifier is said to be free in that expression.
Formulas that contain free variables are called open.

Exercise 2.37, 2.38

2.7 Logical Handling of the Quantifiers

Validities and Equivalents.
Compare the corresponding definitions in section 2.2.
  1. A logical formula is called logically valid if it turns out to be true in every structure.
  2. Formulas are logically equivalent if they obtain he same truth value in every structure.

Exercise 2.39
The propositional version of Exercise 2.19.

Theorem 2.40
1.
  \forall x \forall y \Phi(x,y) \equiv \forall y \forall x \Phi(x,y)
  \exists x \exists y \Phi(x,y) \equiv \exists y \exists x \Phi(x,y)

2.
  not \forall x \Phi(x) \equiv \exists not \Phi(x)
  not \exists x \Phi(x) \equiv \forall not \Phi(x)

3.
  \forall x (\Phi(x) && \Psi(x)) \equiv (\forall x \Phi(x) && \Psi(x))
  \exists x (\Phi(x) || \Psi(x)) \equiv (\exists x \Phi(x) || \Psi(x))

(In chapter 3, partly will be resolved.)

Exercise 2.41 (negation (not \Phi) of 2.36)

Order of Quantifiers.
Theorem 2.40.1 says that the order of similar quantifiers (\forall or \exists) is irrelevant.
But note that this is not the case for different kind of quantifiers.

On the other hand,
  \exists y \forall x \Phi(x,y) ==> \forall x, \exists y \Phi(x,y),
since we can take this same y.
However, if 
  \forall x \exists y \Phi(x,y)
holds, it is far from sure that
  \exists y \forall x \Phi(x,y)
holds as well.

Example 2.42
The statement that
  \forall x \exists y (x<y)
is true in N(natural numbers), but the statement
  \exists y \forall x (x<y)
in this structure wrongly asserts that there exists a greatest natural number. 

Restricted Quantification.

Example 2.43 (Continuity)
The \epsilon-\delta definition of continuity; a real function f:R -> R is continuous if
  \forall x \forall e>0 \exists d>0 \forall y (|x-y|<d ==> |f(x)-f(y)|<e).
This formula uses the restricted quantifiers
  \forall e>0, and \exists d>0
that enable a more compact formulation here.

Example 2.44 (restricted quantification, too much)

Remark.
If A is a subset of the domain of quantification, then
  \forall x \in A \Phi(x)
means the same as
  \forall x (x \in A ==> \Phi(x)),
whereas,
  \exists x \in A \Phi(x)
is tantamount with
  \exists x (x \in A && \Phi(x)).

Warning (==>, &&)

Example 2.45
Some Mersenne number are prime is
  \exists x (M x && P x).
The translation 
  \exists x (M x ==> P x)
is wrong, since it is much too weak, for it expresses that there is a natural number x which is neither a Mersenne nor prime.

In the same way, all prime numbers have irrational sqrt is
  \forall x \in R (P x ==> sqrt x \nin Q).
The translation
  \forall x \in R (P x && sqrt x \nin Q)
is wrong.
This time we end up with something which is too strong, for this expresses hat every real number is a prime number is prime with an irrational sqrt.

Restricted Quantifiers Explained.
Using
  test3 = (\p q -> p ==> q) `logEquiv2` (\p q -> ((not p) || q))
in Theorem 2.10,
  not \forall x \in A \Phi 
    = not \forall x (x \in A ==> \Phi(x))
    = \exists x not (x \in A ==> \Phi(x))
    = \exists x (x \in A && not \Phi(x))
    = \exists x \in A not \Phi(x)

Exercise 2.46
  not \exists x \in A \Phi(x)
    = \forall x \in A not \Phi(x)
    = \exists x \nin A \Phi(x)

Exercise 2.47
  \exists x \nin A not \Phi(x)
    = \forall x \in A \Phi(x)
    
    \= \exists x \in A not \Phi(x)

Exercise 2.48

Example 2.49 (Discontinuity Explained)
  not \forall e>0 \exists d>0 \forall y (|x-y|<d ==> |f(x)-f(y)|<e)
Using Theorem 2.40, this can be transformed in
  \exists e>0 \forall d>0 \exists y not(|x-y|<d ==> |f(x)-f(y)|<e)
According to Theorem 2.10,
  \exists e>0 \forall d>0 \exists y (|x-y|<d && not |f(x)-f(y)|<e)
i.e., 
  \exists e>0 \forall d>0 \exists y (|x-y|<d && |f(x)-f(y)| => e).

Different Sorts.

Exercise 2.50
The sequence a_i (i=0,1,...) in R converges to a means that
  \forall d>0 \exiss n \forall m >= n (|a-a_m|<d).
  
Note:
  Prelude> :type (<=)
  (<=) :: Ord a => a -> a -> Bool
  Prelude> :type (>=)
  (>=) :: Ord a => a -> a -> Bool

The negation is
  not \forall d>0 \exiss n \forall m >= n (|a-a_m|<d)
  \exists d>0 not \exiss n \forall m >= n (|a-a_m|<d)
  \exists d>0 \forall n not \forall m >= n (|a-a_m|<d)
  \exists d>0 \forall n \exists m >= n not (|a-a_m|<d)
Therefore,
  \exists d>0 \forall n \exists m >= n (|a-a_m|>=d).

See 
  http://www.econ.hit-u.ac.jp/~yamada/set_topology1_pdf/note7.pdf
Q.E.D.

2.8 Quantifiers as Procedures

