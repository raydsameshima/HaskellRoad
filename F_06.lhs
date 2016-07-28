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

> comp :: Eq b => [(b,c)] -> [(a,b)] -> [(a,c)]
> g `comp` f = [(x, list2fct g y) | (x,y) <- f]

Fact 6.34
If f : X \to Y, then
  f \circ 1_X = f = 1_Y \circ f

Lemma 6.35
  (h \circ g) \circ f = h \circ (g \circ f)

Lemma 6.36
Suppose that f:X\to Y, g:Y\to Z.
1. g.f injective  ==> f injective
2. g.f surjective ==> g surjective
3. f and g injective  ==> g.f injective
4. f and g surjective ==> g.f surjective

Proof
1.
Let x \neq x' \in X, and
  g.f(x) \neq g.f(x').
If f(x) = f(x'), then clearly g(f(x)) = g(f(x')), but it contradicts.
Therefore
  f(x) \neq f(x'),
and f is injective.

2.
For all z \in Z, there is some x \in X s.t.
  z = g.f(x).
Therefore, for this z, put
  y := f(x) \in Y,
and
  z = g(y).
This means that g is surjective.
  
3.
Let x \neq x' \in X.
Since f is injective,
  f(x) \neq f(x')
and g is also,
  g.f(x) \neq g.f(x').
That is g.f is injective.

4.
If both f and g are surjective, then for arbitrary z \in Z, there is some y s.t.
  z = g(y),
and for this y, there is some x \in X and
  y = f(x).
Therefore, for every z \in Z, there is some x s.t.
  z = g.f(x)
i.e., g.f is surjective.

Q.E.D.

Exercise 6.37

Exercise 6.38
  *F_06> let f = [(0,1),(1,2),(2,0),(3,0),(4,3)]
  *F_06> let func38 = list2fct f
  *F_06> fct2list (func38 . func38) [0..4]
  [(0,2),(1,0),(2,1),(3,1),(4,0)]
  *F_06> fct2list (func38 . func38 . func38 ) [0..4]
  [(0,0),(1,1),(2,2),(3,2),(4,1)]
  *F_06> fct2list (func38 . func38 . func38 . func38) [0..4]
  [(0,1),(1,2),(2,0),(3,0),(4,2)]
  *F_06> fct2list (func38 . func38 . func38 . func38 . func38 ) [0..4]
  [(0,2),(1,0),(2,1),(3,1),(4,0)]

  *F_06> let fList = [(0,1),(1,2),(2,0),(3,0),(4,3)]
  *F_06> fList 
  [(0,1),(1,2),(2,0),(3,0),(4,3)]
  *F_06> fList `comp` it
  [(0,2),(1,0),(2,1),(3,1),(4,0)]
  *F_06> fList `comp` it
  [(0,0),(1,1),(2,2),(3,2),(4,1)]
  *F_06> fList `comp` it
  [(0,1),(1,2),(2,0),(3,0),(4,2)]
  *F_06> fList `comp` it
  [(0,2),(1,0),(2,1),(3,1),(4,0)]

Exercise 6.39
Suppose that A is a finite set and f:A\to A is a bijection.
Then 
  f^1 := f
  f^n := f \circ f^{n-1}, n >= 1

Show that, somewhere in this sequence, there occurs the bijection 1_A.
I.e., a number n exists s.t.
  f^n = 1_A.

Suppose that A has k elements.
Can you give an upper bound for n?

Proof

The cardinality of 
  A^A := {f:A\to A}
is given by
  |A|^|A|,
where |A| is the cardinal, the number of elements, of the set A, and finite.
If there is no such a number n, we could pick infinite many sequence, contradiction.
Therefore, there is some number n s.t.
  f^n = 1_A.

The number of such bijection is the number of permutation of |A| elements.
If we put
  k = |A|
then the number of permutation is
  k!.
The number n can NOT exceed k!.

Q.E.D.

Exercise 6.40
Suppose that h:X \to X satisfies h^3=1_X.
Then h is a bijection.

Proof
Since 1_A is bijection,
  h \circ (h \circ h) = h^3 = (h \circ h) \circ h
is both injective and surjective.
From Lemma 6.36.1, both
  h, h^2
is injective, and from 6.36.2,
  h, h^2
is surjective.
Therefore h and h^2 are bijective.

Q.E.D

(Exercise 6.41 Prove Lemma 6.36.)

Exercise 6.42
Suppose that f:X \to Y and g:Y \to Z are s.t. g\circ f is bijective.
Show that f is surjective iff g is injective.

Proof
From Lemma 6.36, 
  g.f is bijective ==> f injective and g surjective.
If f is surjective, f indeed is bijective, then g is also.
Therefore g is injective.

Similarly, if g is injective, then g is indeed bijective and f is also.
Thus f is surjective.

Q.E.D.

Exercise 6.43
Suppose that 
  \lim_{i \to \infty} a_i = a
and that f:N \to N is injective.
Show that 
  \lim_{i \to \infty} a_{f(i)} = a.

Proof
For arbitrary e>0, there exists n with
  i >= n ==> |a-a_i| < e
(epsilon-N).

We claim that for this n, there exists m with
  \forall k >= m, (f(k) > n),
i.e., 
  m := min {k| f(k) > n }
If there is no such k's, 
  f(k) <= n, forall k,
the domain of f is an infinite subset
  [n,\infty)
and the image is a finite subset
  [0,n]
it contradicts the injectivity of f, since 
  k \= l ==> f(k) \= f(l).

Therefore, for this e>0, there is n s.t.
  k >= n ==> |a-a_{f(k)}| < e,
and
  \lim_{i\to\infty} a_{f(i)} = a.

Q.E.D.

6.4 Inverse Function
Definition 6.44 (Inverse Function)
Suppose that f: X \to Y.
A function g : Y \to X is an inverse of f iff g.f = 1_X and f.g = 1_Y.

Theorem 6.45
A function has at most one inverse.
A function has an inverse iff it is bijective.

Proof
If g,g' : Y \to X are inverses of f, then
  g' = g' . 1_Y
     = g' . f . g
     = 1_X . g
     = g
Therefore, if f has its inverse, it is unique.

From Lemma 3.63, since identities are both injective and surjective,
  g.f = 1_X ==> f injective, g surjective
  f.g = 1_Y ==> g injective, f surjective

Q.E.D.

Notation
If f: X \to Y is a bijection, then its unique inverse is denoted by
  f^{-1} : Y \to X.

Example 6.46 (Celsius v.s. Fahenheit)

> c2f, f2c :: Integral t => t -> t
> c2f x = (9*x) `div` 5 + 32
> f2c x = (5*(x-32)) `div` 9

Left and right inverse.
If g.f = 1_X holds, then g is called the left-inverse of f and f right-inverse of g.

Example 6.47 (fromEnum and toEnum)
fromEnum should be a left-inverse of toEnum.

Excercise 6.48
If f:X \to Y has left-inverse g and right-inverse h, then f is bijective and g=f^{-1}=h.

Proof
Since
  f.g = 1_Y, h.f = 1_X
we have
  h = h . 1_Y
    = h . f . g
    = 1_X . g
    = g
Therefore, g satisfies 
  f.g = 1_Y, g.f = 1_X
and
  g = f^{-1}.
  
Q.E.D.        

Exercise 6.49
Suppose that f:X \to Y and g:Y \to X, then the following are equivalent:
1. g.f = 1_X
2. {(f(x),x) | x \in X} \subset g.

Proof
If g.f=1_X, then an arbitrary x \in X, f(x) goes to
  g.f(x) = x.
So, (f(x),x) \in g.

Conversely, for arbitrary x, if (f(x),x) \in g, then g maps from f(x) to x:
  g(f(x)) = x,
i.e., g.f = 1_X.

Q.E.D.
  
Exercise 6.50
X={0,1}, Y={2,3,4,5}, f={(0,3),(1,4)}.
How many functions g:Y\to X have the proerty, that g.f=1_X?

Since 
  (3,0),(4,1) \in g
but we don't care the others:
  {g': {2,5} \to {0,1}}
This has 2^2 = 4 elements.

Q.E.D.

Exercise 6.51
Give an example of an injection f:X \to Y for which there is no g:Y \to X s.t. g.f = 1_X.

The successor 
  suc: N \to N
is an injection:
  m \= n ==> suc(m) \= suc(n)
for which there is no g:N \to N with g.s = 1_N.

Exercise 6.52
Show that if f:X \to Y is surjective, a function g:Y\to X exists s.t. f.g=1_Y.

Proof
Since f:X \to Y is surjective,
  \forall y \in Y, \exists x \in X s.t. y = f(x),
so \forall y \in Y,
  f^{-1}(y) \subset X
is not empty and
  \cup_{y\in Y} f^{-1}(y) = X
is not empty.
By Axiom of Choice, there is a choice function
  g:Y \to \cup_{y\in Y} f^{-1}(y)
s.t.
  g(y) \in f^{-1}(y).
So
  f(g(y)) = y, \forall y \in Y.

Q.E.D.

Exercise 6.53
How many right-inverses are there to the function
  {(0,5), (1,5), (2,5), (3,6), (4,6)}
(domain={0,1,2,3,4}, codomain={5,6})?

The right-inverse
  g:{5,6} \to {0,1,2,3,4}
satisfies
  f.g(5) = 5 and f.g(6) = 6
So
  g(5) = 0,1,2
  g(6) = 3,4
and there are 3*2 = 6 such right-inverses.

Q.E.D.

Exercise 6.54

Exercise 6.55
Suppose that f:X\to Y is a surjection and h:Y\to X.
Show that the following are equivalent:
1. h is right-inverse of f,
2. h \subset {(f(x),x)| x \in X}

Proof
1.==>2.
Take an arbitrary pair in h:
  \forall (y, h(y)) \in h
then since f.h=1_Y and h(y) \in X,
  (y,h(y)) \in {(f(x),x)| x \in X}
i.e.,
  h \subset {(f(x),x)| x \in X}.

2.==>1.
Since any element in h is the following form
  (f(x),x)
the mapping h satisfies
  \forall y \in Y, \exists x \in X with y = h(x)
  (y=f(x),h(y)=x)
therefore
  \forall y \in Y, f(h(y)) = f(x) = y
and this is equivalent to
  f.h=1_Y.
  
Q.E.D.    

Exercise 6.56
Show 
1. Every function that has a surjective right-inverse is a bijection.
2. Every function that has an injective left-inverse is a bijection.

Proof
1.
Let f:X\to Y with surjective right-inverse
  f.g=1_Y.
From lemma 6.36, f is surjective, and g is injective i.e., g is bijective.
So
  f = g^{-1}
is also bijective.

2.
Let f:X\to Y with injective left-inverse
  h.f=1_X.
From lemma 6.36, h is surjective, i.e., h is bijective:
  f = h^{-1}.

Q.E.D.

6.5 Partial Functions
The computational importance of partial functions is in the systematic perspective they provide on exception handling.

Exercise 6.57
Define a partial function

> stringCompare :: String -> String -> Maybe Ordering
> stringCompare xs ys 
>   | any (not . isAB) (xs++ys) = Nothing
>   | otherwise                 = Just (compare xs ys)
>
> isAB x = x `elem` ['a'..'Z']

6.6 Functions as Partitions
Exercise 6.58
Suppose that f:A\to I is a surjection.
Define the relation R on A by
  aRb :<=> (f(a)=f(b)).
Thus
  R := {(a,b) \in A^2 | f(a)=f(b)}.
Show
1. R is an equivalence on A,
2. A/R = {f^{-1}[{i}] | i \in I},
3. for every equivalence S on A there is a function g on A s.t. aSb <=> g(a)=g(b).

Proof
1.
Since f(a)=f(a),
  aRa, \forall a \in A.
If aRb :<=> f(a)=f(b), then
  f(b)=f(a) <=>: bRa.
If aRb, bRc :<=> f(a)=f(b)=f(c), then
  aRc :<=> f(a)=f(c).
Therefore, R is an equivalence relation on A.

2.
For an arbitrary a \in A, |a|_R \in A/R is
  |a|_R := {a' \in A | aRa' (<=> f(a)=f(a'))}.
Then
  |a|_R \subset A
with
  \forall a' \in |a|_R, f(a')=f(a)
Therefore,
  |a|_R \in {f^{-1}[{i}] | i \in I}.

Conversely, for an arbitrary i \in I,
  f^{-1}(i) = {a \in A| f(a) = i}.
Then
  \forall a' \in f^{-1}(i)
satisfies
  f(a') = i
therefore
  f^{-1}(i) = |a'|_R \in A/R.

Q.E.D.

Example 6.59 (remainder)

Here is a Haskell implementation of a procedure that maps a function to the equivalence relation inducing the partition that corresponds with the function:

> fct2equiv :: Eq a => (t -> a) -> t -> t -> Bool
> fct2equiv f x y = (f x == f y)

Exercise 6.60
Suppose that f:A\to B.
1. Show that if f is injective, then for all sets C and for every g:A\to C there is a function h:B\to C s.t. g=h.f.
2. Show that for all sets C, if to every g:A\to C there is a function h:B\to C s.t. g=h.f, then f is an injection.

Proof
1.
Since f is injective, the co-restriction of f,
  f:A\to f(A)
is bijective, i.e.,
  \forall b \in f(A) \subset B, \exists! a \in A s.t.
  f(a) = b.
Define h':f(A)\to C by
  h'(f(a)) = g(a)
and h:B\to C by
  h = h' (if in f(A))
    = c \in C (of some fixed element in C).
Then clearly,
  h.f(a) = g(a), \forall a \in A.

2.
If we put C=A and g=1_A, then
  h.f=1_A,
and from lemma 6.36, f is injective.

Q.E.D.

Exercise 6.61
Suppose that R is an equivalence relation on A.
Show that for every (sub-)equivalence relation
  S \supset R
on A, there exists a function 
  g:A/R \to A/S
s.t., \forall a \in A,
  |a|_S = g(|a|_R).

Proof
For an arbitrary a \in A,
  |a|_R := {a' \in A | aRa'} \in A/R.
Since S \supset R,
  aRa' <=> (a,a') \in R ==> (a,a') \in S.

What we have to show is that
  g:A/R \to A/S; |a|_R \mapsto |a|_S
is well-defiend; 
  aRa' ==> g(|a|_R) = |a|_S 
                    = |a'|_S
                    = g(|a'|_R)
since (a,a')\in R \subset S.
That is, g does not depend on the representatives, and well-defined.

Q.E.D.

Exercise 6.62
Suppose that ~ is an equivalence relation on A, and that f:A^2\to A is a binary function s.t. for all a,b,x,y\in A,
  a~x \land b~y ==> f(a,b)~f(x,y).
Show that a unique function f^~: (A/~)^2 \to B exists s.t., for a,b \in A,
  f^~(|a|,|b|) = |f(a,b)|.

Proof
What we have to show that f^~ defines a function.
Let
  a~x \land b~y \in A,
then
  |a|=|x| \land |b|=|y| \in A/~
and
  f(a,b)~f(x,y) ==> |f(a,b)|=|f(x,y)|.
That is
  f^~(|a|,|b|) = |f(a,b)| = |f(x,y)| = f^~(|x|,|y|)
and this means that f^~ does not depend on the representatives.

Q.E.D.

Exercise 6.63
Suppose that ~ is an equivalence on A, and that R \subset A^2 is a relation s.t., for all a,b,x,y \in A
  a~x \land b~y \land aRb ==> xRy.
Show that a unique relation R^~ \subset (A/~)^2 exists s.t., for all a,b \in A,
  |a|R^~|b| <=> aRb.

Proof
For arbitrary
  a~x \land b~y
then
  aRb <=> xRy    
Thus
  |a|R^~|b| :<=> aRb
             <=> xRy
             <=> |x|R^~|y|
i.e., R^~ does not depend on the representatives.

Q.E.D.

Exercise 6.64
Let A and B be sets, with B \neq \emptyset.
Define ~ on A\times B by,
  (a,b)~(x,y) :<=> a = x.
1. Show that ~ is an equivalence on A\times B.
2. Exhibit a bijection
     (A\times B)/~ \to A
   from the quotient of A\times B modulo ~ to A.
3. Exhibit, for every equivalence class, a bijection between the class and A.

Proof
1. 
(trivial)

2. 
Define
  p: (A\times B)/~ \to A; |(a,_)| \mapsto a
What we have to show is p is well-defined.
  (a,b)~(x,y) ==> |(a,b)|=|(x,y)|
and
  p(|(a,b)|) = a
             = x
             = p(|(x,y)|)
i.e., p is representative-independent.

3.
Let |(a,b)| be arbitrary.
Define
  q: |(a,b)| \to A; (a,_) \mapsto a
What we have to show is q is well-defined.
Since above definition does not depend on the second argument, q is representative-independent.

Q.E.D.

Equivalence classes (restricted to a list) for an equivalence defined by a function are generated by the following Haskell function:

> block :: Eq a => (t -> a) -> t -> [t] -> [t]
> block f x list = [y| y <- list, f x == f y]
  
  *F_06> block (`rem` 3) 2 [1..20]
  [2,5,8,11,14,17,20]
  *F_06> block (`rem` 7) 4 [1..20]
  [4,11,18]

Exercise 6.65

> fct2listpart :: (a -> Bool) -> [a] -> [[a]]
> fct2listpart bf list = [fList,tList]
>   where tList = filter bf list
>         fList = filter (not . bf) list

  *F_06> fct2listpart even [1..20]
  [[1,3,5,7,9,11,13,15,17,19],[2,4,6,8,10,12,14,16,18,20]]

  *F_06> fct2listpart (\ n -> rem n 3 /= 1) [1..20]
  [[1,4,7,10,13,16,19],[2,3,5,6,8,9,11,12,14,15,17,18,20]]

Exercise 6.66
Give an formula for the number of surjections
  A(^n) \to B(^k).
(Hint: each surjection f:A\to B induces a partition.)

Let f:A\to B be a surjection.
Then
  A = \cup_{b\in B} f^{-1}(b)
is a partition of A.
So, we have nCk partition for this particular f.
There are k! surjections from A/~ to B, where
  a~b <=> f(a)=f(b).
Thus, there are 
  nCk * k!
surjections.

Q.E.D.

6.7 Products
Definition 6.67 (Product)
Suppose that, for every element i\in I a non-empty set X_i is given.
The product
  \prod_{i\in I} X_i
is the set of all functions f for which dom(f)=I and s.t. for all i\in I,
  f(i) \in X_i.

If all X_i (i\in I) are the same,
  X_i = X,
the product is written as
  X^I.
Thus, X^I is the set of all functions f:I\to X.

Exercise 6.68
There are two ways to interpret the expression
  X_0 \times X_1:
1. as \prod_{i\in {0,1}} X_i := {f:{0,1}\to X_0 \times X_1| f(i)\in X_i}
2. as {(x,y) | x \in X_0 \land y \in X_1}
Can you explain why there is no harm in this?

Proof
We write
  (I\to X_0\times X_1)
as the first set and
  {(x,y)}
as the second set.
Then we have a map
  F:(I\to X_0\times X_1) \to {(x,y)}
by
  F(f) := (f(0),f(1))
and
  G:{(x,y)} \to (I\to X_0\times X_1)
by
  G(x,y) := \lambda i.(x_i).
These are inverse pair, since
  G.F(f) = G(f(0),f(1))
         = \lambda i.(f(i))
         = f
and
  F.G(x,y) = F(\lambda i.(x_i))
           = (x_0, x_1)
           = (x,y)
Q.E.D.

Exercise 6.69
Let A be any set.
Exhibit two different bijection between p(A) of power sets and {0,1}^A.

If we identify
  0 = False
  1 = True
then

  F:p(A) \to {0,1}^A; X \mapsto \lambda a. (a\in A \land a \in X)
  G:p(A) \to {0,1}^A; X \mapsto \lambda a. (a\in A \land a \not\in X)

Q.E.D.

Exercise 6.70
On the set of functions
  Y^X := {f:X\to Y},
the relation \sim is defined by:
  f \sim g :<=> \exists i:Y\to Y, j:X\to X (bijections) s.t.
  i.f = g.j

1. Show that \sim is an equivalence relation.
2. Show: if f,g:X\to Y are injective, then f\sim g.

Proof
1.
(reflexive) for all f:X\to Y,
  f.1_X = f = 1_Y.f
(symmetry) if f \sim g, i.e.,
  i.f = g.j
then, since i,j are bijective,
  f.j^{-1} = i^{-1}.g <=> g \sim f
(transitive) let f \sim g, g \sim h, i.e., there are bijectives with
  i.f = g.j
  k.g = h.l
then (from the commutative diagrams),
  (k.i).f = k.g.j
          = h.(l.j)
and
  f \sim h.

2.
Since f:X\to Y is injective, the co-restriction
  f':X\to f(X)
is bijective, and if we define
  i':f(X)\to Y; f(x) \mapsto g(x)
then we have
  i.f = g.1_X,
where
  i(y) = i'(y), if y \in f(X) (i.e., i(f(x)) = g(x))
       = y      otherwise
Therefore, if f,g:X\to Y is injective, then
  f \sim g.

Q.E.D.
          
Exercise 6.71
Suppose that X,Y and Z are sets and
  h:Y\to Z.
then
  h\circ -: Y^X \to Z^X; g \mapsto h\circ g
if h is injective(surjective), then h\circ - is also injective(surjective).

Proof
If for g,g'\in Y^X,
  h\circ -(g) = h\circ -(g')
i.e.,
  h\circ (g) = h\circ (g')







