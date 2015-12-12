STAL_04.lhs

Chapter 4
Sets, Types and Lists

> module STAL_04 where
> import Data.List 
> import DB
> import SetEq

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

Theorem 4.20 (complement)

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
Take A:=\cup F, then
  \forall X(X \in F ==> X \subset \cup F)
    <=> \forall X(X \in F ==> X \in 2^(\cup F))
    <=> F \subset 2^(\cup F)
and 
  \forall x \in A := \cup F
    <=> \exists X \in F s.t. x \in X
now, if F \subset 2^B, then
  x \in X \in F \subset 2^B,
i.e. x \in X \subset B.
Thus \forall x \in A => x \in B and
  A \subset B.

Q.E.D.

Remark
If the index set 
  I = \emptyset,
then 
  \cup_{i \in I} A_i = \emptyset
  \cap_{i \in I} A_i = {the collection of all sets}
Therefore, the second notation usually presupposes that I \neq \emptyset.

Example 4.28 (DeMorgan law)

Exercise 4.29 (Theorem 4.20 (complement))

Exercise 4.30
  2^\emptyset = {\emptyset} "singleton"
or more simply
  2^{} = {{}}

  2^(2^{}) = 2^{{}}
           = {{}, {{}}}

  2^(2^(2^{})) = 2^{{}, {{}}}
               = {{}, {{}}, {{{}}}, {{},{{}}}}
The number of 
  (2^)^5({})
is
  2^5 = 32

  #(2^A) = 2^(#A)

Exercise 4.31
  A = B <=> 2^A = 2^B

Proof
(==>)
  \forall U \in 2^A
    <=> U \subset A = B
    <=> U \in 2^B
Therefore A=B ==> 2^A=2^B.

(<==)
Let us take \forall a \in A, i.e.,
  {a} \in 2^A = 2^B 
    <=> a \in B
Therefore 2^A=2^B ==> A=B.

Q.E.D.

Exercise 4.32
1. 2^(A \cap B) = 2^A \cap 2^B

  \forall X \in 2^(A \cap B)
    <=> X \subset (A \cap B)
    <=> X \subset A && X \subset B
    <=> X \in (2^A \cap 2^B)

2.
But if we change \cap -> \cup, then

  \forall X \in 2^(A \cup B)
    <=> X \subset (A \cup B)
    <== X \subset A || X \subset B
          <=> X \in (2^A \cup 2^B)

i.e. 2^(A \cup B) \supset (2^A \cup 2^B)

Q.E.D.

Exercise 4.33

Exercise 4.34
Any sequence of sets
  A_0, A_1, ...
with 
  2^A_{i+1} \subset A_i
is finite.

Proof (Russel's set)
Let us define
  A_{i+1} <- A_i :<=> 2^A_{i+1} \subset A_i.
Suppose there is an infinite sequence
  ... <- A_2 <- A_1 <- A_0
Then we can show that
  2^{\cap_{i \in N} A_i} \subset \cap_{i \in N} A_i
since for B := \cap_{i \in N} A_i,
  2^B = 2^{\cap_{i \in N} A_i}
      = {x| x \subset \cap_{i \in N} A_i} 
      = {x| \forall x \in N, x \subset A_i}
      \subset {x| \forall x \in N, x \subset A_{i+1}}
      = {x| \forall x \in N, x \in 2^A_{i+1}}
      \subset {x| \forall x \in N, x \in A_i}
      = \cap_{i \in N} A_i
      = B
That is B has the following property:
  2^B \subset B
and we can construct the Russel set
  { R\in B | R \nin R }
This gives us a contradiction.

Q.E.D.

Exercise 4.35 (recursive definition)
K :: the collection of sets with
  \forall A \in K(A = \emptyset || \exists B \in K (A=2^B))
then
  \forall A \in K, \exists n \in N, A = power^n(B)

Proof
Since A is either \emptyset or the form of
  2^B, B \in K,
this B is also in K and B is also either \emptyset or 2^C, C \in K form.
This procedure will terminate since we've prove it in Exercise 4.34, so at some point they will hit an \emptyset.
Therefore
  \forall A \in K, \exists n \in N, A = power^n(B)

Q.E.D.
 
4.5 Ordered Pairs and Products
Ordered pairs behave according to the following rule:
  (a,b) = (x,y) ==> a=x && b=y 

Defining Ordered Pairs.
  (a,b) := {{a},{a,b}}

Definition 4.36 (Products)
The (Cartesian) product of sets A and B is the
  A \times B := {(a,b) | a \in A && b \in B}

Example 4.37

Theorem 4.38, 4.39

Exercise 4.40

Exercise 4.41

Definition 4.42 (n-tuples over A)
1. A^0 := {\emptyset}
2. A^{n+1} := A \times A^n

4.6 Lists and List Operation
Assuming the list elements are all taken from a set A, the set of all lists over A is the set 
  A^* := \cup_{n \in N} A^n
For every list
  L \in A^*
there is some n \in N with
  L \in A^n,
and if L \in A^n, we say that list L has length n.

In Haskell the data type of lists is (pre-)declared like

  *STAL_04> :info []
  data [] a = [] | a : [a]  -- Defined in ‘GHC.Types’

and the equality of the lists is that of elements, i.e. extensionality:

  instance Eq a => Eq [a] where
    []     == []     = True
    (x:xs) == (y:ys) = x==y && xs==ys
    _      == _      = False

Exercise 4.43
How does it follow from this definition that lists of different length are unequal?

Answer: Will hit the third case.

A type of class Ord is a type on which the two-placed operation compare is defined, with a result of type Ordering.

  *STAL_04> :info Ordering 
  data Ordering = LT | EQ | GT  -- Defined in ‘GHC.Types’

The following piece of Haskell code implements of compare:
  
  instance Ord a => Ord [a] where
    compare [] (_:_) = LT
    compare [] []    = EQ
    compare (_:_) [] = GT
    compare (x:xs) (y:ys) -- non-emptysets will hit here
      = primCompAux x y (compare xs ys)

    primCompAux :: Ord a => a -> a -> Ordering -> Ordering
    primCompAux x y o =
      case compare x y of EQ -> o;
                          LT -> LT;
                          GT -> GT

Exercise 4.44
Another ordering of lists is as follows: shorter lists come before longer ones, and for lists of the same length we compare their first elements, and if these are the same, the remainder lists.
Give a formal definition of this ordering.

> compare' :: Ord a => [a] -> [a] -> Ordering
> compare' [] [] = EQ
> compare' xx yy
>   | length xx < length yy = LT
>   | length xx > length yy = GT
>   | otherwise             = compare xx yy

Exercise 4.45

> init' [x] = []
> init' (x:xs) = x: init xs

Exercise 4.46 (reverse)
A naive implementation is the following:

> myReverse :: [a] -> [a]
> myReverse [] = []
> myReverse (x:xs) = myReverse xs ++ [x]

This is slow, and the Prelude's implementation is

foldl (flip (:)) [] 

Cool.

Exercise 4.47
Write a function splitList that gives all the ways to split a list of at least two element in two non-empty parts.

> splitList' :: [a] -> [([a],[a])]
> splitList' [] = error "give me non-empty list"
> splitList' [x] = error "sorry, more elements" 
> splitList' [x,y] = [([x],[y])]
> -- splitList' (x:y:ys) = ([x],(y:ys)) : splitList' (y:ys)
> splitList' (x:y:ys) = ([x],(y:ys)) : map (f x) splittedList
>   where splittedList = splitList' (y:ys)
>         f x (z,w) = (x:z,w)

The basic idea is the same as the solution.

An operation on lists that we will need in the next sections is the operation or removing duplicates.
This is predefined in Haskell module as nub ("nub" means essence), but here is a home-made version

> nub' :: (Eq a) => [a] -> [a]
> nub' []     = []
> nub' (x:xs) = x : nub (remove' x xs)
>   where remove' y [] = []
>         remove' y (z:zs) 
>           | y == z    = remove' y zs
>           | otherwise = z : remove' y zs

4.7 List Comprehension and Database Query
The database can be used to define the following lists of database objects, with list comprehension.
Here db :: DB is the database list, where we have imported DB as
  import DB
on the top of this file.

> characters = nub [x | ["play",_,_,x] <- db]
> movies     =     [x | ["release",x,_] <- db]
> actors     = nub [x | ["play",x,_,_] <- db]
> directors  = nub [x | ["direct",x,_] <- db]
> dates      = nub [x | ["release",_,x] <- db]
> universe   = nub (characters ++ actors ++ directors ++ movies ++ dates)

Next, define lists of tuples, again by list comprehension:

> direct  = [(x,y) | ["direct",x,y] <- db]
> act     = [(x,y) | ["play",x,y,_] <- db]
> play    = [(x,y,z) | ["play",x,y,z] <- db]
> release = [(x,y) | ["release",x,y] <- db]

Finally, define one placed, two placed and three placed predicates by means of lambda abstraction.

> charP = \x -> elem x characters
> actorP = \x -> elem x actors
> movieP = \x -> elem x movies
> directorP = \x -> elem x directors
> dataP = \x -> elem x dates
> actP = \(x,y) -> (x,y) `elem` act
> releaseP = \(x,y) -> (x,y) `elem` release
> directP = \(x,y) -> (x,y) `elem` direct
> playP = \(x,y,z) -> (x,y,z) `elem` play

We start with some conjunctive queries.
"Give me the actors that also are directors."

> q1 = [x | x <- actors, directorP x]

"Give me all actors that also are directors, together with the films in which they were acting."

> q2 = [(x,y) | (x,y) <- act, directorP x]

"Give me all directors together with their films and their release dates."
The follwoing is wrong:

> q3 = [(x,y,z) | (x,y) <- direct, (y,z) <- release] 

The problem is that the two y's are unrelated.
In fact, this query generates an infinite list.
This can be remedied by using the equality predicate as a link:

> q4 = [(x,y,z) | (x,y) <- direct, (u,z) <- release, y==u]

"Give me all directors of films released in 1995, together with these films."

> q5 = [(x,y) | (x,y) <- direct, (u,"1995") <- release, y==u]

"Give me all directors of films released after 1995, together with these films and their dates."

> q6 = [(x,y,z) | (x,y) <- direct, (u,z) <- release, y==u, z>"1995"]

"Give me the films in which Kevin Spacey acted."

> q7 = [x | ("Kevin Spacey",x) <- act]

"Give me all films released after 1997 in which William Hurt did act."

> q8 = [x | (x,y) <- release, y > "1997", actP ("William Hurt",x)]

Yes/no queries based on conjunctive querying: "Are these any films in which the director was also an actor?"

> q9 = q1 /= []

"Does the database contain films directed by Woody Allen?"

> q10 = [x | ("Woody Allen",x) <- direct ] /= []
> q10' = directorP "Woody Allen"

Exercise 4.48
"Give me the films in which Robert De Niro or Kevin Spacey acted."

> q11 = [(x,y) | ["play",x,y,_] <- db, x == "Robert De Niro" || x== "Kevin Spacey"]

Exercise 4.49
"Give me all films with Quentin Tarantino as actor or director that appeared in 1994"

> q12 = nub [title | ["play",y,title,_] <- db, ["direct",y,title] <- db, ["release",title,"1994"] <- db, y=="Quentin Tarantino"]

Exercise 4.50
"Give me all films released after 1997 in which William Hurt did not act."

> q13 = [title | (title, year) <- release, year > "1997", not . actP $ ("William Hurt", title)]

4.8 Using Lists to Represent Sets
Sets are unordered, lists are ordered, but we can use lists to represent finite or countably infinite sets by representing sets as lists with duplicates removed, and by disregarding the order.

To remove the first occurrence of the element from the list, delete function is built in Data.List.

> delete' :: Eq a => a -> [a] -> [a]
> delete' _ [] = []
> delete' x (y:ys) 
>   | x == y    = ys
>   | otherwise = y : (delete x ys) 

As we've seen, the operation of elem for finding elements is also built in.

> isElem :: Eq a => a -> [a] -> Bool
> _ `isElem` [] = False
> x `isElem` (y:ys)
>   | x == y    = True
>   | otherwise = x `isElem` ys

Further operations on sets that we need to implement are union, intersection and difference.
These are all built in, the following are home-made versions.

> union', intersect' :: Eq a => [a] -> [a] -> [a]
> union' []     ys = ys
> union' (x:xs) ys 
>   = x : union xs (delete x ys) 

> intersect' [] ys = []
> intersect' (x:xs) ys
>   | x `isElem` ys = x : intersect' xs ys
>   | otherwise     = intersect' xs ys 

Exercise 4.51
The Haskell operation for list difference is predefined as (\\) in Data.List.
  *STAL_04> [1,2,3] \\ [2,3,4]
  [1]
  *STAL_04> [1,2,3,5] \\ [2,3,4]
  [1,5]
  *STAL_04> [1,2,3,5] \\ [0,2,3,4]
  [1,5]

> difference :: Eq a => [a] -> [a] -> [a]
> difference xs []     = xs 
> difference xs (y:ys) = difference (delete' y xs) ys

The predefined versions of the functions elem(isElem) and notElem(isNotElem) for testing whether an object occurs in a list, or not, use the function any and all:

> isElem', isNotElem' :: Eq a => a -> [a] -> Bool
> isElem'    = any . (==)
> isNotElem' = all . (/=)

Be cautions, they are ill-terminat functions.

Let's turn to an operation for the list of all sublists of a given list.

> addElem :: a -> [[a]] -> [[a]]
> addElem x = map (x:)

> powerList :: [a] -> [[a]]
> powerList [] = [[]]
> powerList (x:xs) = (powerList xs) ++ (map (x:) (powerList xs))

E.g, 
  filterM (\x -> [True, False])
is also powerList function.

The follwoing is from 
https://www.reddit.com/r/programming/comments/225f0/beautiful_haskell_implementation_of_maths_power

> powerList' :: [a] -> [[a]]
> powerList' [] = [[]]
> powerList' (x:xs) = do
>   xxs <- powerList' xs
>   [x:xxs, xxs]  

This is the fold-version of above simple recursion:

> powerList'' :: [a] -> [[a]]
> powerList'' = foldr (\x xs -> xs ++ map (x:) xs) [[]]

Examle 4.52
Lists in Haskell is much less flexisble than set theory about types.

Exercise 4.53
Write genUnion and genIntersect for generalized list union and list intersection.
  genUnion, genIntersect :: Eq a => [[a]] -> [a]

genUnion :: Eq a => [[a]] -> [a]
genUnion = foldl union' []

This implementation is different from the solutions:

genIntersect :: Eq a => [[a]] -> [a]
genIntersect = foldl intersect []

> genUnion :: Eq a => [[a]] -> [a]
> genUnion [] = []
> genUnion [xs] = xs
> genUnion (xs:xss) = union xs (genUnion xss)

> genIntersect :: Eq a => [[a]] -> [a]
> genIntersect [] = error "list of lists should be non-empty"
> genIntersect [xs] = xs
> genIntersect (xs:xss) = intersect xs (genIntersect xss)

Union behaves samely:

*STAL_04> genUnion ["map", "aaaa", "aiueo"]
"mapiueo"
*STAL_04> foldl union' [] ["map", "aaaa", "aiueo"]
"mapiueo"

4.9 A Data Type for Sets
A list representation of "sets": SetEq.hs.

  *STAL_04> Set [1,2,3] == Set [3,2,1]
  True
  *STAL_04> Set [1..] == Set [1]
  False
  *STAL_04> Set [1,1..] == Set [1]
  ^CInterrupted.
  *STAL_04> Set [x | x <- [1,1,1,1,1]] == Set [1]
  True

But still have bad points.
  *STAL_04> (Set $ powerList [1..3]) == (powerSet $ Set [1..3])
  
  <interactive>:30:30:
  Couldn't match type ‘Set Integer’ with ‘[Integer]’
  Expected type: Set [Integer]
    Actual type: Set (Set Integer)
  In the second argument of ‘(==)’, namely
    ‘(powerSet $ Set [1 .. 3])’
  In the expression:
    (Set $ powerList [1 .. 3]) == (powerSet $ Set [1 .. 3])
  In an equation for ‘it’:
    it = (Set $ powerList [1 .. 3]) == (powerSet $ Set [1 .. 3])

  *STAL_04> powerSet $ Set [1..3]
  {{},{3},{2},{2,3},{1},{1,3},{1,2},{1,2,3}}
  *STAL_04> Set $ powerList [1..3]
  {[],[3],[2],[2,3],[1],[1,3],[1,2],[1,2,3]}
  *STAL_04> :type powerSet $ Set [1..3]
  powerSet $ Set [1..3] :: (Enum a, Eq a, Num a) => Set (Set a)
  *STAL_04> :type Set $ powerList [1..3]
  Set $ powerList [1..3] :: (Enum a, Num a) => Set [a]  

Exercise 4.54 (unionSet, intersectSet, diffrenceSet)
Exercise 4.55 (insertSet without duplicates)
