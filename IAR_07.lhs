IAR_07.lhs

Induction and Recursion

> module IAR_07 where

> import Data.List
> import STAL_04 (display)

7.1 Mathematical Induction
1. Basis (Base case)
Prove that 0 has the property P.
  P(0)
2. Induction step
Assume the induction hypothesis that n has property P.
Prove on the basis of this that n+1 has property P.
  P(n) ==> P(n+1)

The goal
  \forall n \in N, P(n)
follows from this by the principle of mathematical induction:

Fact 7.1
For every set
  X \subset N
we have that
  0 \in X and \forall n \in N(n\in X) ==> n+1 \in X) ==> X=N.

Example 7.2 Sum of the Angles of a Convex Polygon.
The angle of a convex polygon of (n+3) sides is (n+1)*\pi radians.

Proof
Base case
For n=0, it holds, since any triangle has \pi as the sum of the angles.

Induction step
Assume the sum of the angles of a convex polygon of (n+3) sides is (n+1)*\pi radians.
Consider a convex polygon P of (n+4) sides.
Connecting 1st and 3rd edges, we can decompose P into a polygon P' of (n+3) sides and a triangle T'.
The sum of the angles of P equals the sum of P' and T':
  (n+1)*\pi + \pi = (n+1+1)*\pi

From the principle of mathematical induction, the statement follows.

Q.E.D.

Example 7.3
The sum of the first n odd numbers.

\sum_{k=1}^n (2*k-1) = n^2

> sumOdds, sumOdds' :: Integer -> Integer
> sumOdds' n = sum [2*k-1 | k<-[1..n]]
> sumOdds  n = n^2

  *IAR_07> and (map (\n -> sumOdds' n == sumOdds n) [1..1000])
  True

Example 7.4
The sum of the first n even numbers.

\sum_{k=1}^n 2*k = n*(n+1)

> sumEvens, sumEvens' :: Integer -> Integer
> sumEvens' n = sum [2*k | k<-[1..n]]
> sumEvens  n = n*(n+1)

> sumInts n = sumEvens n `div` 2

Example 7.5, Exercise 7.6
Summing squares.

\sum_{k=1}^n k^2 = n*(n+1)*(2*n+1)/6

> sumSquares, sumSquares' :: Integer -> Integer
> sumSquares' n = sum [k^2 | k<-[1..n]]
> sumSquares  n = n*(n+1)*(2*n +1) `div` 6

Example 7.7, Exercise 7.8
Summing cubes.

\sum_{k=1}^n = (n*(n+1)/2)^2

> sumCubes, sumCubes' :: Integer -> Integer
> sumCubes' n = sum [k^3 | k<-[1..n]]
> sumCubes  n = (n*(n+1) `div` 2)^2

Exercise 7.9
Prove that for all n \in N, 3^(2*n+3) + 2^n is divisible by 7.

Proof
Base case (n=0)
3^3 + 1 = 28 = 7*4

Induction step
Let us assume 
  3^(2*n+3)+2^n = 7*k, k\in N
Then
  3^(2*(n+1)+3)+2^(n+1)
   = 3^(2*n+3+2)+2^(n+1)
   = 9*3^(2*n+3)+2*2^n
   = 9*(7*k -2^n) +2*2^n
   = 9*7*k + (2-9)*2^n
   = 7*(9*k-2^n)
Therefore, from the principle of mathematical induction, the statement holds.

Q.E.D.

Remark(well-founded)
For any A that is well-founded by a relation < the following principle holds.
Let X \subset A, if
  \forall a \in A(\forall b < a(b\in X) ==> a \in X),
then X=A.

7.2 Recursion over the Natural Numbers

> data Natural = Zero
>              | Succ Natural
>              deriving (Eq, Show)

The recursive definition of addition on the natural numbers.
1. m+0     := m
2. m+(n+1) := (m+n)+1

> plus :: Natural -> Natural -> Natural
> m `plus` Zero = m
> m `plus` (Succ n) = Succ (m `plus` n) 

We can prove the following list of fundamental laws of addition:
  m+0     = m       (0 as the additive identity element)
  m+n     = n+m     (commutativity)
  m+(n+k) = (m+n)+k (associativity)

Proposition 7.10
\forall m,n,k \in N,
  m+(n+k) = (m+n)+k (associativity)

Proof
We prove it induction on k.

Base case
  m+(n+0) = m+n     (+.1.)
          = (m+n)+0 (+.1.)

Induction step
Assume
  m+(n+k) = (m+n)+k
then
  m+(n+(k+1)) = m+((n+k)+1) (+.2.)
              = (m+(n+k))+1 (+.2.)
              = ((m+n)+k)+1 (i.h.)
              = (m+n)+(k+1) (+.2.)
Therefore, from the principle of mathematical induction, the statement holds.

Q.E.D.

Proposition 7.11
\forall m,n \in N,
  m+n = n+m (commutativity)

Proof
We prove it induction on n.

Base case (n=0)
Induction on m.
  Base case (m=0)
    0+0 = 0 = 0+0

  Indunction step
  Let us assume 
    m+0 = 0+m
  then
    (m+1)+0 = m+1 (+.1.)
            = (m+0)+1 (+.1.)
            = (0+m)+1 (i.h.)
            = 0+(m+1) (associativity) 
  So \forall m \in N,
    m+0 = 0+m.

Induction step
Assume
  m+n = n+m
then
  m+(n+1) = (m+n)+1 (+.2.)
          = (n+m)+1 (i.h.)
          = n+(m+1) (+.2.)
          = n+(1+m) (i.h.)
          = (n+1)+m (associativity)
Therefore, commutativity for addition on natural numbers holds.

Q.E.D.

Once we have addition, we can define multiplication:
1. m*0     := 0
2. m*(n+1) := (m*n)+m    

> mult :: Natural -> Natural -> Natural
> m `mult` Zero = Zero
> m `mult` (Succ n) = (m `mult` n) `plus` m

> natural2Int :: Natural -> Int
> natural2Int Zero = 0
> natural2Int nat = helper nat 0
>   where helper Zero n = n
>         helper (Succ m) n = helper m (n+1)

  *IAR_07> Succ (Succ Zero) `mult` Succ (Succ (Succ Zero))
  Succ (Succ (Succ (Succ (Succ (Succ Zero)))))
  *IAR_07> natural2Int it
  6

The operation for exponentiation on naturals is also recursive:

> expn m Zero = (Succ Zero) 
> expn m (Succ n) = (expn m n) `mult` m

  *IAR_07> expn (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))
  Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))
  *IAR_07> natural2Int it
  8

Exercise 7.13
Prove by mathematical induction that
  k^(m+n) = k^m*k^n

Proof
Induction on n.
Base case (n=0)
  k^(m+0) = k^m
          = k^m * 1
          = k^m * k^0
Induction step
Let us assume
  k^(m+n) = k^m*k^n
then
  k^(m+(n+1)) = k^((m+n)+1)
              = k^(m+n) * k
              = k^m * k^m * k
              = k^m * k^(m+1)
Therefore, the statement holds.               

Q.E.D.

We can define the relation <= on N as follows
  m <= n :<=> \exists k \in N, m+k=n.
We use
  m < n
for
  m <= n \land m \neq n

> leq Zero     _        = True
> leq (Succ _) Zero     = False
> leq (Succ m) (Succ n) = leq m n

> geq m n = leq n m
> gt m n = not $ leq m n
> lt m n = gt n m

Exercise 7.14 (cut-off subtraction)

> subtrN :: Natural -> Natural -> Natural
> subtrN Zero _    = Zero
> subtrN m    Zero = m
> subtrN (Succ m) (Succ n) = subtrN m n

Exercise 7.15 (quotient and remainder on naturals)

> quotientN, remainderN :: Natural -> Natural -> Natural
> quotientN _ Zero = error "quotientN: zero-division"
> quotientN m n
>   | gt n m    = m
>   | otherwise = quotientN (m `subtrN` n) n
> 
> remainderN m n = m `subtrN` m'
>   where
>     m' = (quotientN m n) `mult` m

7.3 The Nature of Recursive Definitions
The format:
  f(0)   := c
  f(n+1) := h(f(n))

The general procedure is easily implemented in an operation foldn, defined as follows:

> foldn :: (a -> a) -> a -> Natural -> a
> foldn h c Zero     = c
> foldn h c (Succ n) = h (foldn h c n)

> exclaim :: Natural -> String
> exclaim = foldn ('!':) []

> plus' = foldn (\n -> Succ n)
> mult' m = foldn (plus' m) Zero
> expn' m = foldn (mult' m) (Succ Zero)

Exercise 7.16

> subtr' = foldn pre
>
> pre :: Natural -> Natural
> pre Zero     = Zero
> pre (Succ n) = n

Exercise 7.17 (Fibonacci)
For all n > 1,
  F_{n+1} * F_{n-1} - (F_n)^2 = (-1)^n.

Proof
Base case (n=2)
  F_3 * F_1 - (F_2)^2 = 2*1 - 1^2 = 1 = (-1)^2

Induction step
Assume 
  F_{n+1} * F_{n-1} - (F_n)^2 = (-1)^n
then
  F_{n+2} * F_n - (F_{n+1})^2 
   = (F_n+F_{n+1})*F_n - (F_{n+1})^2
   = (F_n)^2 - F_{n+1}*(F_{n+1}-F_n)
   = (F_n)^2 - F_{n+1}*F_{n-1}
   = -(-1)^n
   = (-1)^{n+1}
Therefore, from the principle of mathematical induction, the statement follows.

Q.E.D.

Exercise 7.18
A bitlist is a list of zeros and ones.
Consider the following code bittest for selecting the bitlist without consecutive zeros.

> bittest :: [Int] -> Bool
> bittest []       = True
> bittest [0]      = True
> bittest (1:xs)   = bittest xs
> bittest (0:1:xs) = bittest xs
> bittest _        = False

1.
How many bitlists of length 0(1,2,3) satisfy bittest?

2.
Let a_n be the number of bitlists of length n without consecutive zeros.
Give an induction proof to show that for every n >= 0 it holds that
  a_n = F_{n+2},
where F_n is the n-th Fibonacci number.

length 0 : []
length 1 : [0], [1]
length 2 : [1,0], [1,1], [0,1]
length 3 : [0,1,0], [0,1,1], [1,0,1], [1,1,0], [1,1,1]

So the list of a_n is
  [1,2,3,5, ..

For length = 0,1,
  a_0 = 1 = F_2
  a_1 = 2 = F_3
In general, a_n is given by
  a_n = a_{n-1} -- (0:xs) 
      + a_{n-2} -- (0:1:xs)
Since the initial conditions are the same as Fibonacci, we have
  a_n = F_{n+2}

Q.E.D.

Exercise 7.19
Show that the following two implementations are the same.

> fib 0 = 0
> fib 1 = 1
> fib n = fib (n-1) + fib (n-2)

> fib' n = fib2 0 1 n
>   where
>     fib2 a _ 0 = a
>     fib2 a b n = fib2 b (a+b) (n-1)

Base case
  *IAR_07> fib' 0
  0
  *IAR_07> fib' 1
  1

Induction step
Now
  fib2 (fib i) (fib (i+1)) n
   = fib2 (fib (i+1)) (fib i + fib (i+1)) (n-1)
   = fib2 (fib (i+1) (fib (i+2)) (n-1)
   = fib2 (fib (i+2) (fib (i+3)) (n-2)
   = ...
   = fib2 (fib (i+n)) (fib (i+n+1)) 0
   = fib (i+n)
holds for arbitrary i,n \in N.

So 
  fib' n = fib2 0 1 n
         = fib2 (fib 0) (fib 1) n
         = fib (0+n)
         = fib n

Q.E.D.

Exercise 7.20 (The Catalan numbers)

> catalan :: Int -> Int
> catalan 0 = 1
> catalan n = sum [ (catalan i) * (catalan (n-1-i)) | i <- [0..(n-1)]]

Exercise 7.21
Let x_0 .. x_n be a sequence of (n+1) variables.
Suppose their product is to be computed by doing n multiplications.
The number of ways to do the multiplications corresponds to the number of bracketings for the sequence.
Say,
  (x_0 x_1)(x_2 x_3)
  ((x_0 x_1) x_2) x_3
  (x_0 (x_1 x_2)) x_3
  x_0 ((x_1 x_2) x_3)
  x_0 (x_1 (x_2 x_3))

Show that the number of bracketings for (n+1) variables is given by the Catalan number C_n.

Proof
Base case.
For (0+1) variable case, we have only 1 bracketing:
  x_0
i.e., no bracketing.

Induction step
Let n be an arbitrary natural number.
Assume for any i with
  0 <= i <= n,
for any sequence of (i+1) variables have C_i bracketings.

Consider the order of multiplications, say the first example has
  x_0 ((x_1 x_2) x_3)
   = x_0 (x_{12} x_3)
   = x_0 (x_{123})
   = x_{0123}
For (n+1+1) variables case, pick x_{i+1} up.
Then 
  x_0 .. x_i
has
  C_i
bracketings, and
  x_{i+2} .. x_{n+1}
has
  C_{n+1-(i+2)} = C_{n+1-i}
bracketings.
Therefore the number of bracketings for (n+1+1) variables is
  \sum_{0<=i<=n} C_i * C_{n+1-i}
This is the same recursion relation for the Catalan numbers.

Q.E.D.

Example 7.22
Balanced sequences of 2*n parentheses has C_n different combinations

7.4 Induction and Recursion over Trees
Example 7.23
The number of nodes of a binary tree of depth d is
  2^{d+1}-1.

Here is a Haskell implementation of binary trees:

> data BinTree = LeafB
>              | NodeB BinTree BinTree
>              deriving (Show, Eq)
>
> makeBinTree :: Integer -- depth
>             -> BinTree
> makeBinTree 0 = LeafB
> makeBinTree n = NodeB (makeBinTree (n-1)) (makeBinTree (n-1))
>
> count :: BinTree -> Integer
> count LeafB = 1
> count (NodeB tl tr) = 1 + count tl + count tr

  *IAR_07> makeBinTree 3
  NodeB (
       NodeB (
            NodeB LeafB LeafB
            ) 
            (
            NodeB LeafB LeafB
            )
       ) 
       (
       NodeB (
            NodeB LeafB LeafB
            ) 
            (
            NodeB LeafB LeafB
            )
       )

> depth :: BinTree -> Integer
> depth LeafB = 0
> depth (NodeB tl tr) = 1+ max (depth tl) (depth tr)
>
> isBalanced :: BinTree -> Bool
> isBalanced LeafB = True
> isBalanced (NodeB tl tr) = isBalanced tl
>                         && isBalanced tr
>                         && depth tl == depth tr

Example 7.24 
Counting the Nodes of a Balanced Ternary Tree.
  \sum_{k=0}^n 3^k = \frac{3^{n+1} -1}{2}

Example 7.25

> data TernaryTree = TLeaf 
>                  | TNode TernaryTree TernaryTree TernaryTree
>                  deriving (Show, Eq)
>
> makeBalancedTTree :: Integer     -- depth
>                   -> TernaryTree
> makeBalancedTTree 0 = TLeaf
> makeBalancedTTree n = TNode (makeBalancedTTree (n-1)) 
>                             (makeBalancedTTree (n-1))
>                             (makeBalancedTTree (n-1))
>
> countTTree :: TernaryTree -> Integer
> countTTree TLeaf = 1
> countTTree (TNode t1 t2 t3)
>   = 1 + countTTree t1 + countTTree t2 + countTTree t3

Example 7.26
Counting the Nodes of a Balanced m-ary Tree.

Example 7.27
Geometric Progressing.

Tree with integers at the nodes:

> data Tree = Lf
>           | Nd Int Tree Tree
>           deriving (Show, Eq)

Ordered trees
We say that a tree is ordered iff it holds for each node N of the tree that the integers in the left sub-tree below N and all smaller than the number at node N, and the number in the right sub-tree below N are all greater than the number at N.

> insertTree :: Int -> Tree -> Tree
> insertTree n Lf = Nd n Lf Lf
> insertTree n t@(Nd m t1 t2)
>   | n < m     = Nd m (insertTree n t1) t2
>   | n > m     = Nd m t1 (insertTree n t2)
>   | otherwise = t

  *IAR_07> foldr insertTree Lf [5, 3, 6, 2, 9, 1, 4, 7, 8]
  Nd 8 (
       Nd 7 (
            Nd 4 (
                 Nd 1 Lf (
                         Nd 2 Lf 
                              (Nd 3 Lf Lf)
                         )
                 ) 
                 (
                 Nd 6 (
                      Nd 5 Lf Lf
                      ) 
                      Lf
                 )
            ) 
            Lf
       ) 
       (
       Nd 9 Lf Lf
       )

Exercise 7.29

> list2tree :: [Int] -> Tree
> list2tree = foldr insertTree Lf 

In the case of list, fordr is defined as
  foldl f z [] = z
  foldl f z (x:xs) = foldl f (f z x) xs
that is
  foldl f z [w,x,y] = foldl f (f z w) [x,y]
                    = foldl f (f (f z w) x) [y]
                    = foldl f (f (f (f z w) x) y) []
                    = (f (f (f z w) x) y)
                    
> tree2list :: Tree -> [Int]
> tree2list Lf = []
> tree2list (Nd n t1 t2) = tree2list t1 ++ [n] ++ tree2list t2
  
  *IAR_07> foldr insertTree Lf [8, 3, 6, 2, 9, 1, 4, 7, 5]
  Nd 5 (Nd 4 (Nd 1 Lf (Nd 2 Lf (Nd 3 Lf Lf))) Lf) (Nd 7 (Nd 6 Lf Lf) (Nd 9 (Nd 8 Lf Lf) Lf))
  *IAR_07> tree2list it
  [1,2,3,4,5,6,7,8,9]
                    
Exercise 7.30

> isInTree :: Int -> Tree -> Bool
> isInTree _ Lf = False
> isInTree n (Nd m t1 t2)
>   | n == m  = True
>   | n <  m  = isInTree n t1 -- Tree is ordered
>   | n >  m  = isInTree n t2

Exercise 7.31

> mergeTrees :: Tree -> Tree -> Tree
> mergeTrees t1 t2 = foldr insertTree t2 (tree2list t1)
  
  *IAR_07> let t1 = Nd 3 (Nd 2 Lf Lf) (Nd 5 Lf Lf)
  *IAR_07> let t2 = Nd 4 (Nd 1 Lf Lf) (Nd 6 Lf Lf)
  *IAR_07> mergeTrees t1 t2
  Nd 4 (
       Nd 1 Lf 
            (
            Nd 3 (
                 Nd 2 Lf Lf
                 ) 
                 Lf
            )
       ) 
       (
       Nd 6 (
            Nd 5 Lf Lf
            ) 
            Lf
       )

> mergeTrees' t1 t2 = list2tree l12
>   where
>     l12 = l1 ++ l2
>     l1 = tree2list t1
>     l2 = tree2list t2
  
  *IAR_07> let t1 = Nd 3 (Nd 2 Lf Lf) (Nd 5 Lf Lf)
  *IAR_07> let t2 = Nd 4 (Nd 1 Lf Lf) (Nd 6 Lf Lf)
  *IAR_07> mergeTrees' t1 t2
  Nd 6 (Nd 4 (Nd 1 Lf (Nd 3 (Nd 2 Lf Lf) Lf)) (Nd 5 Lf Lf)) Lf

Exercise 7.32

> findDepth :: Int -> Tree -> Int
> findDepth _ Lf = -1    -- default value
> findDepth n (Nd m l r)
>   | n == m = 0
>   | n <  m = if d1 == -1 then -1 else d1+1
>   | n >  m = if d2 == -1 then -1 else d2+1
>   where
>     d1 = findDepth n l
>     d2 = findDepth n r

A general data type for binary trees with information at the internal nodes is given by:

> data Tr a = Nil
>           | T a (Tr a) (Tr a)
>           deriving (Eq, Show)

Exercise 7.33

> mapT :: (a -> b) -> Tr a -> Tr b
> mapT f Nil = Nil
> mapT f (T v t1 t2) = T (f v) (mapT f t1) (mapT f t2)

Exercise 7.34

> foldT :: (a -> b -> b -> b) -> b -> (Tr a) -> b
> foldT _ z Nil = z
> foldT f z (T v t1 t2) = f v (foldT f z t1) (foldT f z t2)

Exercise 7.35

> preorderT, inorderT, postorderT :: Tr a -> [a]
> preorderT = foldT preLists []
>   where
>     preLists x ys zs = (x:ys) ++ zs
> inorderT = foldT inLists []
>   where
>     inLists x ys zs = ys ++ (x:zs)
> postorderT = foldT postLists []
>   where
>     postLists x ys zs = ys ++ zs ++ [x]

Exercise 7.36

> isOrderedT :: Ord a => Tr a -> Bool
> isOrderedT tree = isOrderedL (inorderT tree)
> isOrderedL :: Ord a => [a] -> Bool
> isOrderedL lst = (sort . nub $ lst) == lst

Exercise 7.37
An ordered tree can be used as a dictionary by putting items of type
  (String, String)
at the internal nodes, and defining the ordering as
  (v,w) <= (v',w') iff v <= v'.

> type Dict = Tr (String, String)
>
> lookupD :: String -> Dict -> [String]
> lookupD _ Nil = []
> lookupD s (T (t1,t2) leftT rightT)
>   | s == t1 = [t2]
>   | s <  t1 = lookupD s leftT
>   | s >  t1 = lookupD s rightT

Exercise 7.38
For efficient search in an ordered tree, it is crucial that the tree is balanced, i.e., the left and right subtree should have (nearly) the same depth and should themselves be balanced.

> split :: [a] -> ([a],a,[a])
> split [] = error "split: give non-empty list"
> split xs = (ys,y, ys')
>   where
>     ys      = take n xs
>     (y:ys') = drop n xs
>     n       = length xs `div` 2

> data LeafTree a = Leaf a
>                 | Node (LeafTree a) (LeafTree a)
>                 deriving (Show, Eq)

> ltree :: LeafTree String
> ltree = Node (Leaf "I")
>              (Node (Leaf "love")
>                    (Leaf "you"))

Exercise 7.39

> mapLT :: (a -> b) -> LeafTree a -> LeafTree b
> mapLT f (Leaf a) = Leaf (f a)
> mapLT f (Node t1 t2) = Node (mapLT f t1) (mapLT f t2)

Exercise 7.40

> reflect :: LeafTree a -> LeafTree a
> reflect t@(Leaf a) = t
> reflect (Node t1 t2) = Node (reflect t2) (reflect t1)

Exercise 7.41
Prove
  reflect . reflect $ t == t

A data type for trees with arbitrary numbers of branches, with information of type a at the buds, is given by:

> data Rose a = Bud a
>             | Br [Rose a]
>             deriving (Eq, Show)
>
> rose = Br [Bud 1, Br [Bud 2, Bud 3, Br [Bud 4, Bud 5, Bud 6]]]

  *IAR_07> :t rose
  rose :: Rose Integer

Exercise 7.42

> mapR :: (a -> b) -> Rose a -> Rose b
> mapR f (Bud x) = Bud (f x)
> mapR f (Br xs) = Br (map (mapR f) xs)

  *IAR_07> rose
  Br [Bud 1,Br [Bud 2,Bud 3,Br [Bud 4,Bud 5,Bud 6]]]
  *IAR_07> mapR succ rose
  Br [Bud 2,Br [Bud 3,Bud 4,Br [Bud 5,Bud 6,Bud 7]]]

7.5 Induction and Recursion over Lists

> len :: [a] -> Int
> len [] = 0
> len (x:xs) = 1 + len xs

> cat :: [a] -> [a] -> [a]
> cat []     ys = ys
> cat (x:xs) ys = x: (cat xs ys)

Proposition 7.43
For all lists xs, ys, and zs over the same type a,
  cat (cat xs ys) zs == cat xs (cat ys zs).

Proof
Induction on xs.
Base case.
  cat (cat [] ys) zs == cat ys zs
  cat [] (cat ys zs) == cat ys zs

Induction step
Let us assume
  cat (cat xs ys) zs == cat xs (cat ys zs)
then
  cat (cat (x:xs) ys) zs
  == cat (x:(cat xs ys)) zs
  
  cat (x:xs) (cat ys zs)
  == x: (cat xs (cat ys zs))
  == x: (cat (cat xs ys) zs)
  == cat (x:(cat xs ys)) zs

Therefore, we have
  cat (cat (x:xs) ys) zs == cat (x:xs) (cat ys zs)
and from the principle of mathematical induction (on lists), the statements follows.

Q.E.D.

Exercise 7.44
Prove by induction that
  cat xs [] = cat [] xs

Proof
Base case
  cat [] [] == cat [] []

Induction step
Let us assume
  cat xs [] == cat [] xs
then by definition, they are equal to
  xs
and
  cat (x:xs) [] == x:(cat xs [])
                == x:(cat [] xs)
                == (x:xs)
  cat [] (x:xs) == (x:xs)

Therefore, from the principle of mathematical induction, the statement holds.

Q.E.D.

Exercise 7.45
Prove by induction:
  len (cat xs ys) == (len xs) + (len ys)

Proof
Base case
  len (cat [] ys) == len ys
                  == 0 + len ys
                  == len [] + len ys

Induction step
Assuming
  len (cat xs ys) == len xs + len ys
then
  len (cat (x:xs) ys) == len (x: cat xs ys)
                      == 1 + len (cat xs ys)
                      == 1 + len xs + len ys
                      == len (x:xs) + len ys
Therefore, from the principle of mathematical induction, the statement follows.

Q.E.D.

A general scheme for structural recursion over lists is foldr:

> myFoldr :: (a -> b -> b) -> b -> [a] -> b
> myFoldr _ z [] = z
> myFoldr f z (x:xs) = f x (myFoldr f z xs)

> add = myFoldr plus Zero -- add :: [Natural] -> Natural
> mlt = myFoldr mult (Succ Zero)
>
> ln :: [a] -> Natural
> ln = myFoldr (\_ n -> Succ n) Zero

Exercise 7.46

> genUnion :: Eq a => [[a]] -> [a]
> genUnion = foldr union []
> 
> genIntersect :: Eq a => [[a]] -> [a]
> genIntersect = foldr1 intersect

Exercise 7.47

> srt :: Ord a => [a] -> [a]
> srt = foldr insrt []
>
> insrt :: Ord a => a -> [a] -> [a]
> insrt y [] = [y]
> insrt y xx@(x:xs)
>   | y <  x = y:xx
>   | y >= x = x:(insrt y xs)

Left-fold (foldl) can be used to speed up list processing.

> myFoldl :: (a -> b -> a) -> a -> [b] -> a
> myFoldl _ z [] = z
> myFoldl f z (x:xs) = myFoldl f (f z x) xs

Reversing a list

> prefix :: [a] -> a -> [a]
> prefix ys y = y:ys
>
> revl = myFoldl prefix []

  revl [1,2,3] 
  == foldl prefix [] [1,2,3]
  == foldl prefix (prefix [] 1) [2,3]
  == foldl prefix [1] [2,3]
  == foldl prefix (prefix [1] 2) [3]
  == foldl prefix [2,1] [3]
  == foldl prefix (prefix [2,1] 3) []
  == foldl prefix [3,2,1] []
  == [3,2,1]

Here is an alternative implementation of reverse, using postfix:

> postfix :: a -> [a] -> [a]
> postfix y ys = ys ++ [y]
>
> revr = myFoldr postfix []

The inefficiency resides in the fact that (++) itself is defined recursively:

  []     ++ ys = ys
  (x:xs) ++ ys = x:(xs ++ ys)

To see why revr is less efficient thatn revl, observe revr [1,2,3]:

  revr [1,2,3]
  == foldr postfix [] [1,2,3]
  == postfix 1 (foldr postfix [] [2,3])
  == (foldr postfix [] [2,3]) ++ [1]
  == (postfix 2 (foldr postfix [] [3])) ++ [1]
  == (foldr postfix [] [3]) ++ [2] ++ [1]
  == (postfix 3 (foldr postfix [] [])) ++ [2] ++ [1]
  == foldr postfix [] [] ++ [3] ++ [2] ++ [1]
  == [] ++ [3] ++ [2] ++ [1]
  == [3] ++ [2] ++ [1]
  == 3: ([] ++ [2]) ++ [1]
  == 3:[2] ++ [1]
  == [3,2] ++ [1]
  == 3:([2] ++ [1])
  == 3:2:([] ++ [1])
  == 3:2:[1]
  == 3:[2,1]
  == [3,2,1]

Exercise 7.48
Let
  h  :: a -> b -> b
  h' :: b -> a -> b
  z  :: b
Assume that for all
  x :: a,
it holds that
  h x (h' y z) = h' z (h x y).
Show that for every
  x,y :: a
  xs :: [a]
the following holds:
  h x (foldl h' y xs) == foldl h' (h x y) xs

Proof
We prove by induction on xs.

Base case (xs == [])
  h x (foldl h' y []) == h x y
  foldl h' (h x y) [] == h x y

Induction step
Let us assume for xs case, 
  h x (foldl h' y xs) == foldl h' (h x y) xs
then
  h x (foldl h' y (z:xs))
   == h x (foldl h' (h' y z) xs)
   == foldl h' (h x (h' y z)) xs  (i.h.)
   == foldl h' (h' (h x y) z) xs
   == foldl h' (h x y) (z:xs)
Thus, the statement follows.

Q.E.D.

Example 7.49
Let
  h  :: a -> b -> b
  h' :: b -> a -> b
  z  :: b.
Assume we have for all x,y :: a and xs :: [a], the following
  h x z = h' z x
  h x (h' y z) == h' z (h x y)
Show that for all finite xs :: [a] that
  foldr h z xs == foldl h' z xs.

Proof
We prove by induction on xs.

Base case (xs == [])
  foldr h z [] == z == foldl h' z []

Induction step.
Let us assume
  foldr h z xs == foldl h' z xs
then
  foldr h z (x:xs)
   == h x (foldr h z xs)
   == h x (foldl h' z xs)
   == foldl h' (h x z) xs (by 7.48)
   == foldl h' (h' z x) xs
   == foldl h' z (x:xs)

Q.E.D.

Note
The functions postfix and prefix satisfy these conditions.
Therefore, rev and rev' compute the same function.

Exercise 7.50 (accumulator)
Consider the following version of rev

> rev1 :: [a] -> [a] 
> rev1 xs = rev2 xs []
>   where
>     rev2 []     ys = ys
>     rev2 (x:xs) ys = rev2 xs (x:ys)

This pattern-match is indeed the same as left-fold (foldl), and therefore rev1 is essentially the same as rev(foldl).

Q.E.D.

Exercise 7.51
Define an alternative version ln' of 
  ln = myFoldr (\_ n -> Succ n) Zero
using foldl instead of foldr.

> ln' :: [a] -> Natural
> ln' = foldl (\n _ -> Succ n) Zero

Exercise 7.52
Let 
  xs :: [a] 
  f :: a -> b 
and
  p :: b -> Bool
be total predicate.
Show
  filter p (map f xs) == map f (filter (p . f) xs).

Proof
We prove by induction xs.

Base case.
  filter p (map f [])
   == filter p []
   == []

  map f (filter (p . f) [])
   == map f []
   == []

Induction step
Assume xs case, then
  filter p (map f (x:xs))
   == filter p ((f x): map f xs)
   == if (p (f x)) then (f x): filter p (map f xs)
                   else        filter p (map f xs)
  
  map f (filter (p . f) (x:xs))
   == map f (if ((p . f) x) then x: filter (p . f) xs
                            else    filter (p . f) xs)
   == if ((p . f) x) then (f x): map f (filter (p . f) xs)
                     else        map f (filter (p . f) xs)

Since we have assume
  filter p (map f xs) == map f (filter (p . f) xs)
they are the same.

Q.E.D.

7.6 Some Variations on the Tower of Hanoi

Exercise 7.53
We prove by induction
  hanoi n = 2^n -1.

Base case (n=1)
2^(1) -1 = 2-1 = 1.

Induction step.
Let us assume 
  hanoi n(>=1) = 2^n-1,
then consider (n+1)-disks case.
Let us move first n-disks to one place (from A to B), we take 2^n-1 steps.
Now we move the last, largest disk toward the destination (C), then move n-disks from B to C, i.e.,
  2^n-1
  +1
  +2^n -1
  == 2*2^n -1
  == 2^{n+1}-1

Q.E.D.

? Exercise 7.54(1 <= k <= n hanoi)

Exercise 7.55
  
  *IAR_07> 2^64 -1
  18446744073709551615
  *IAR_07> it / (365.25)
  5.050443278223012e16

So 5*10^16 years.

An implementation of the disk transfer procedure, we represent the starting configuration of the Hanoi-tower
  ([1..8],[],[]).

> data Peg = A | B | C
> type Tower = ([Int],[Int],[Int])
>
> move :: Peg -> Peg -> Tower -> Tower
> move A B ((x:xs), ys, zs) = (xs, (x:ys), zs)
> move A C ((x:xs), ys, zs) = (xs, ys, (x:zs))
> move B A (xs, (y:ys), zs) = ((y:xs), ys, zs)
> move B C (xs, (y:ys), zs) = (xs, ys, (y:zs))
> move C A (xs, ys, (z:zs)) = ((z:xs), ys, zs)
> move C B (xs, ys, (z:zs)) = (xs, (z:ys), zs)

> transfer :: Peg   -- initial peg 
>          -> Peg   -- destination
>          -> Peg 
>          -> Int   -- the number of distks to move 
>          -> Tower -- the tower configuration to move
>          -> [Tower]
> transfer _ _ _ 0 tower = [tower]
> transfer p q r n tower =
>   transfer p r q (n-1) tower -- one-step before
>   ++
>   transfer r q p (n-1) (move p q tower')
>     where
>       tower' = last (transfer p r q (n-1) tower)
>
> hanoi n = transfer A C B n ([1..n], [], [])
