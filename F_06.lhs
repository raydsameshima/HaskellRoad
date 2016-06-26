F_06.lhs

Chapter 6
Functions

> module F_06 where
> import Data.List

Example 6.1

> f x = x^2 + 1

> absReal x
>   | x >= 0    = x
>   | otherwise = -x

> identity :: a -> a
> identity x = x

Definition 6.2
A function f:X -> Y is a relation f \subset X\timex Y that satisfies the following condition.
  (x,y) \in f and (x,z) \in f ==> y==z
That is, for every x \in dom(f), there is exactly one y \in ran(f) s.t. (x,y) \in f.

> list2fct :: Eq a => [(a,b)] -> a -> b
> list2fct [] _ = error "list2fct: functions should be total"
> list2fct ((u,v):uvs) x
>   | x == u    = v
>   | otherwise = list2fct uvs x
>
> fct2list :: (a -> b) -> [a] -> [(a,b)]
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

Definition 6.4
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

