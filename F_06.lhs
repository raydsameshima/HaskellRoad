F_06.lhs

Chapter 6
Functions

> module F_06 where
> import Data.List

Example 6.1

> f x = x^2 + 1 -- f :: Num a => a -> a

> absReal x -- absReal :: (Num a, Ord a) => a -> a
>   | x >= 0    = x
>   | otherwise = -x

> identity :: a -> a
> identity x = x

Definition 6.2
A function f:X -> Y is a relation f \subset X\timex Y that satisfies the following condition.
  (x,y) \in f and (x,z) \in f ==> y==z
That is, for every x \in dom(f), there is exactly one y \in ran(f) s.t. (x,y) \in f.

> -- list2fct :: Eq a => [(a,b)] -> a -> b
> list2fct :: Eq a => [(a,b)] -> (a -> b)
> list2fct [] _ = error "list2fct: functions should be total"
> list2fct ((u,v):uvs) x
>   | x == u    = v
>   | otherwise = list2fct uvs x
>
> fct2list :: (a -> b) 
>          -> [a]      -- domain 
>          -> [(a,b)]
> fct2list f xs = [(x, f x) | x <- xs]

The range of a function, implemented as a list of pairs:

> ranPairs :: Eq b => [(a,b)] -> [b]
> ranPairs f = nub [y | (_,y) <- f]

If a function is defined on an enumerable domain, we can list its (finite or infinite) range starting from a given element.

> listValues :: Enum a => (a -> b) -> a -> [b]
> listValues f i = (f i) : listValues f (succ i)

If we also know that the domain is bounded, we can generate the whole range as a finite list.

> listRange :: (Bounded a, Enum a) => (a -> b) -> [b]
> listRange f = [f i | i <- [minBound .. maxBound]]

Definition 6.4 (From ...to, On, Co-domain)
  f:X \to Y

Fact 6.5 (Function equality)
If f and g are functions that share their domain 
  dom(f) = X = dom(g)
and, on it, carry out the same transform, i.e. forall x \in X,
  f(x) == g(x)
then,
  f == g
according to Extensionality.

Recurrences versus closed forms
Example 6.9

> g 0 = 0
> g n = g (n-1) + n
>
> g' n = ((n+1)*n)/2

Exercise 6.10
Give a closed form implementation of the following function.

> h 0 = 0
> h n = h (n-1) + (2*n)

> h' n = (n+1)*n

Exercise 6.11

> k 0 = 0
> k n = k (n-1) + (2*n -1)
>
> k' n = n^2

It is not always possible to find useful definitions in closed form, and recurrences are in general much easier to find than closed forms.
Computationally, there is nothing to choose between the following two implementation of the factorial of n.

> fact 0 = 1
> fact n = n * fact (n-1)
>
> -- product [] is normalized as 1.
> fact' n = product [k | k <- [1..n]]

Definition 6.12 (Restrictions)

> restrict :: Eq a => (a -> b) -> [a] -> a -> b
> restrict f xs x
>   | x `elem` xs = f x
>   | otherwise   = error "restrict: argument is not in the domain"
>
> restrictPairs :: Eq a => [(a,b)] -> [a] -> [(a,b)]
> restrictPairs xys xs = [(x,y) | (x,y) <- xys, x `elem` xs]

Definition 6.13 (Image, co-image)
For f:X \to Y, A \subset X, and B \subset Y,
  f[A] := {f(x) | x \in A}
is called the image of A under f,
  f^{-1}[B] := {x \in X| f(x) \in B}
            = f^{\from}[B]
is called the called the co-image or inverse-image of B under f.

> image :: Eq b => (a -> b) -> [a] -> [b]
> image f xs = nub [f x | x <- xs]
>
> coImage :: Eq b => (a -> b) -> [a] -> [b] -> [a]
> coImage f xs ys = [x | x <- xs, (f x) `elem` ys]
>
> imagePairs :: (Eq a, Eq b) => [(a,b)] -> [a] -> [b]
> imagePairs f xs = image (list2fct f) xs
> 
> coImagePairs :: (Eq a, Eq b) => [(a,b)] -> [a] -> [b] -> [a]
> coImagePairs f xs ys = coImage (list2fct f) xs ys

Exercise 6.15
R={(0,4),(1,2),(1,3)} is not a function, but R^{-1} is.

Exercise 6.16

> xList = [0..4]
> yList = [2..5]
> fPairs = [(0,3),(1,2),(2,4),(3,2)]

  *F_06> restrictPairs fPair [0,3]
  [(0,3),(3,2)]
  *F_06> restrictPairs fPair [1,2,3]
  [(1,2),(2,4),(3,2)]> 
  *F_06> coImage f xList [2,4,5]
  [1,2]

> l_0 = [(0,3),(1,2),(2,4),(3,2)]
> f_0 = list2fct l_0
> test_1 = fct2list (restrict f_0 [0,3]) [0,3]
> test_2 = image f_0 [1,2,3]
> test_3 = coImage f_0 [0..3] [2,4,5]

Exercise 6.17
Suppose that
  f: A \to Y, g: B \to Y
and
  A \cap B = \emptyset
Show that 
  f \cup g : A \cup B \to Y
What if A \cap B \neq \emptyset?

Proof
Since
  f = {(a, y)| a \in A, y = f(a)} \subset A \times Y
we have
  f \cup g = {(a,f(a))|a \in A} \cup {(b,g(b))|b \in B}
Since A \cap B = \emptyset, for arbitrary c \in (A \cup B), either
  c \in A or c \in B,
and in either case, there exists a unique
  f(c) or g(c) \in Y
that is, f\cup g is a function that has 
  A \cup B \to Y.

In case A \cap B \neq \emtpyset, f\cup g is a function iff f==g on (A \cap B), i.e., the restriction are the same function:
  f|(A\cap B) == g|(A\cap B)
  
Q.E.D.

Exercise 6.18
Since a partition FA of X are a set of disjoint subset of X, if there existsa function
  f_A: A \to Y, \forall A \in FA,
then
  \cup_{A \in FA} f_A : X \to Y
is a function.

Example 6.19
Suppose f:X \to Y, and A,B \subset X.
Then f[A -B] \supset f[A] -f[B].

Take
  y \in f[A] - f[B]
then 
  y \in f[a] and y \not \in f[B].
From the 1st case,
  \exists x \in A s.t. y = f(x).
From the 2nd case,
  x \not \in B
So,
  x \in A - B
and
  y = f(x) \in f[A-B]

Exercise 6.20.1
For f:X \to Y, A,B\subset X, C,D \subset Y,
  C \subset D \Rightarrow f^{-1}[C] \subset f^{-1}[D].

Proof
Since
  f^{-1}[C] := {x \in X | f(x) \in C}
  f^{-1}[D] := {x \in X | f(x) \in D}
if x \in f^{-1}[C], then
  f(x) \in C \subset D
and 
  x \in f^{-1}[D].

Q.E.D.

Exercise 6.20.2
  f[A\cup B] = f[A]\cup f[B]
  f[A\cap B] \subset f[A]\cap f[B]

Proof
  f[A\cup B] = {f(x) \in Y | x \in A or x \in B}
             = {f(x) \in Y | x \in A} \cup {f(x) \in Y | x \in B}
             = f[A] \cup f[B]
              
If y \in f[A\cap B], then there exists
  x \in X s.t. y = f(x)
and
  x \in A\cap B
that is
  x \in A and x \in B
and
  y=f(x) \in f[A] and y=f(x) \in f[B].
  
Q.E.D.

Exercise 6.20.3
  f^{-1}[C \cup D] = f^{-1}[C] \cup f^{-1}[D]
  f^{-1}[C \cap D] = f^{-1}[C] \cap f^{-1}[D]

Proof
  f^{-1}[C \cup D] = {x \in X | f(x) \in C \cup D}
                   = {x \in X | f(x) \in C or f(x) \in D}
                   = {x \in X | f(x) \in C} \cup {x \in X | f(x) \in D}
                   = f^{-1}[C] \cup f^{-1}[D]

The similar argument holds for \cap.

Q.E.D.

Exercise 6.20.4
  f[f^{-1}[C]] \subset C
  f^{-1}[f[A]] \supset A

Proof
If we choose
  y \in f[f^{-1}[C]], 
then there exists 
  x \in f^{-1}[C] s.t. y=f(x)
and
  y=f(x) \in C.
   
Next, let us choose
  a \in A
and by definition,
  f(a) \in f[A].
Then clearly
  a \in f^{-1}[f[A]].

Q.E.D.

6.2 Surjections, Injections, Bijections

Definition 6.21 (Surjections, Injections, Bijections)
A function f: X \to Y is called

1. surjective, iff every element b \in Y, there exists (at least one) a \in X s.t.
  b = f(z).
I.e., f[X] = Y;

2. injective, iff every b\in Y is value of at most one a \in X;

3. bijective, iff both injective and surjective.

Example 6.22

If the domain of a function is represented as a list, the injectivity test can be implemented as follows:

> injective :: Eq b => (a -> b) -> [a] -> Bool
> injective f [] = True
> injective f (x:xs) = notElem (f x) (image f xs)
>                   && injective f xs

Similarly, if both the domain and co-domain of a function are represented as lists, the surjectivity test can be implemented as follows:

> surjective :: Eq b => (a -> b) -> [a] -> [b] -> Bool
> surjective f xs [] = True
> surjective f xs (y:ys) = y `elem` (image f xs)
>                       && surjective f xs ys

Exercise 6.23

> bijective :: Eq b => (a -> b) -> [a] -> [b] -> Bool
> bijective f xs ys = (injective f xs) && (surjective f xs ys)

Exercise 6.24
Implement tests for functions represented as lists of pairs.

> injectivePairs :: (Eq a, Eq b) => [(a,b)] -> [a] -> Bool
> injectivePairs f xs = injective (list2fct f) xs
>
> surjectivePairs :: (Eq b, Eq a) => [(a, b)] -> [a] -> [b] -> Bool
> surjectivePairs f xs ys = surjective (list2fct f) xs ys
>
> bijectivePairs :: (Eq a, Eq b) => [(a, b)] -> [a] -> [b] -> Bool
> bijectivePairs f xs ys = (injectivePairs f xs)
>                       && (surjectivePairs f xs ys)

Proving that a function is injective/surjective.
The following implication is a useful way of expressing that f is injective:  f(x) = f(y) ==> x = y
  x \= y ==> f(x) \= f(y)

Exercise 6.25

Exercise 6.26
Give a formula for the number of injections from an n-element set A to a k-element set B.

The number is given by
  k P n := k*(k-1)* ... (k-n+1)
        
Exercise 6.27
Implement a function that produces the list of all injections from finite domain and codomain.

> injs :: [Int] -- finite domain
>      -> [Int] -- finite co-domain
>      -> [[(Int,Int)]]
> injs _ [] = []
> injs [] _ = [[]]
> injs (x:xs) ys = concat [map ((x,y):) (injs xs (ys \\ [y])) | y <- ys]

Exercise 6.28
The bijections on a finite set A correspond exactly to the permutations on A.
Implement a function that gives all permutation of a finite list.

> perms :: [a]   -- finite
>      -> [[a]]
> perms [] = [[]]
> perms (x:xs) = concat $ map (insrt x) (perms xs)
>
> insrt :: t -> [t] -> [[t]]
> insrt x [] = [[x]]
> insrt x yy@(y:ys) = (x:yy) : map (y:) (insrt x ys)

> -- from http://www.geocities.jp/m_hiroi/func/haskell06.html
> select :: [a] -> [(a,[a])]
> select [] = []
> select (x:xs) = (x,xs): [(y,x:ys)| (y,ys) <- select xs]
>
> perms' :: [a] -> [[a]]
> perms' [] = [[]]
> perms' xs = [y:zs| (y,ys) <- select xs, zs <- perms' ys]

6.3 Function Composition
Definition 6.29 (Composition)
Example 6.30, 6.31

Example 6.32
Implemen an operation comp for composition of functions represented as lists of pairs.

> comp :: [(a,b)] -> [(b,c)] -> [(a,c)]
> comp = undefined




