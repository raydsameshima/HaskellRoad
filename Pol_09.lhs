Pol_09.lhs

Chapter 9

> module Pol_09 where

> import GHC.Real
> import Polynomials

9.1 Difference Analysis of Polynomial Sequences

Suppose {a_n}_n is a sequence of natural numbers, i.e.,
  a := \n -> a_n
is a function in N\to N.

The function f is a polynomial function of degree k iff f can be presented in the form
  c_k*n^k + .. c_1*n + c_0,
with c_i \in Q and c_k \= 0.

Example 9.1

  *> take 10 $ map (\n -> 2*n^2+n+1) [0..]
  [1,4,11,22,37,56,79,106,137,172]

Consider the difference sequence given by
  d(f) = \n -> a_{n+1} - a_n

> difs :: [Integer] -> [Integer]
> difs []            = []
> difs [_]           = []
> difs (a:bb@(b:bs)) = b-a : difs bb

  *> take 15 $ map (\n -> 2*n^2+n+1) [0..]
  [1,4,11,22,37,56,79,106,137,172,211,254,301,352,407]
  *> difs it
  [3,7,11,15,19,23,27,31,35,39,43,47,51,55]
  *> difs it
  [4,4,4,4,4,4,4,4,4,4,4,4,4]

Proposition 9.2
If f is a polynomial function of degree k then
  difs f
is a polynomial function of degree (k-1).

Proof
Suppose f(n) is given by
  c_k*n^k + .. c_1*n + c_0,
Then difference sequence of f is
  f(n+1) - f(n)
   == c_k*(n+1)^k + o(n^(k-1))
       - c_k*n^k - o(n^(k-1) 
   == c_k*k*n^{k-1} + o(n^(k-1))
where o is small-o notation.

Q.E.D.

It follows this proposition, if f is a polynomial function of degree k, thend^k(f) will be a constant function (of degree 0).

Charles Babbage (1791-1871), one of the founding fathers of computer science, used the followings in the design of his difference engine.

The following function keeps generating difference lists until the differences get const:

> difLists :: [[Integer]] -> [[Integer]]
> difLists [] = []
> difLists lst@(l:ls) =
>   if const l then lst
>              else difLists $ (difs l):lst
>   where
>     const (n:mm@(m:ms)) 
>             = all (==n) mm
>     const _ = error "difList: lack of data or not a polynomial function"
  
  *> take 15 $ map (\n -> 2*n^2+n+1) [0..]
  [1,4,11,22,37,56,79,106,137,172,211,254,301,352,407]
  *> difLists [it]
  [[4,4,4,4,4,4,4,4,4,4,4,4,4]
  ,[3,7,11,15,19,23,27,31,35,39,43,47,51,55]
  ,[1,4,11,22,37,56,79,106,137,172,211,254,301,352,407]
  ]

The following function gets the list of last elements that we need:

> genDifs xs = map last $ difLists [xs]

  *> difLists [[-12,-11,6,45,112,213,354,541,780,1077]]
  [[6,6,6,6,6,6,6]
  ,[16,22,28,34,40,46,52,58]
  ,[1,17,39,67,101,141,187,239,297]
  ,[-12,-11,6,45,112,213,354,541,780,1077]
  ]
  *> genDifs [-12,-11,6,45,112,213,354,541,780,1077]
  [6,58,297,1077]

> nextD :: [Integer] -> [Integer]
> nextD []       = error "nextD: no data"
> nextD [n]      = [n]
> nextD (n:m:ms) = n : nextD (n+m:ms)

The next element of the original sequence is given by the last element of the new list of last elements of difference lists:

> next = last . nextD . genDifs

  *> next [-12,-11,6,45,112,213,354,541,780,1077]
  1438

> continue xs = map last $ iterate nextD differences
>   where
>     differences = nextD $ genDifs xs

The function iterate is given by
  iterate f x =  x : iterate f (f x)
              = [x, f x, f (f x), ..] 

  *> take 20 $ continue [-12,-11,6,45,112,213,354,541,780,1077] 
  [1438,1869,2376,2965,3642,4413,5284,6261,7350,8557,9888,11349,12946,14685,16572,18613,20814,23181,25720,28437]

> degree xs = length (difLists [xs]) -1

  *> difLists[ [-12,-11,6,45,112,213,354,541,780,1077]]
  [[6,6,6,6,6,6,6],[16,22,28,34,40,46,52,58],[1,17,39,67,101,141,187,239,297],[-12,-11,6,45,112,213,354,541,780,1077]]
  *> map degree it
  [0,1,2,3]

Exercise 9.3

9.2 Gaussian Elimination

If we know that a sequence has a polynomial form of degree 3:
  a + b*x + c*x^2 + d*x^3
then we can solve it for a,b,c,d:
  a_0 == a
  a_1 == a + b + c + d
  a_2 == a + 2*b + 4*c + 8*d
  a_3 == a + 3*b + 9*c + 27*d
(Since this is a set of four linear equations in four unknowns.)

Example 9.4, 9.5

Solving sets of linear equations can be viewed as manipulation of matrices of coefficients.
To solve the following coefficients,
  [[1,0,0,0,a_0]
  ,[1,1,1,1,a_1]
  ,[1,2,4,8,a_2]
  ,[1,3,9,27,a_3]
  ]
we transform it to left triangular form (or so called echelon form):
  [[a00,a01,a02,a03,b0]
  ,[0,a11,a12,a13,b1]
  ,[0,0,a22,a23,b2]
  ,[0,0,0,a33,b3]
  ]


> type Matrix = [Row]
> type Row    = [Integer]

> rows, cols :: Matrix -> Int
> rows = length
> cols m
>   | m == []   = 0
>   | otherwise = length $ head m

> genMatrix :: [Integer] -> Matrix
> genMatrix xs = zipWith (++) (genM d) [[x] | x <- xs]
>   where
>     d = degree xs
>     genM n = [[toInteger x^m | m <- [0..n]] | x <- [0..n]]

  *Pol_09> genMatrix [13, 21, 35, 55, 81, 113, 151]
  [[1,0,0,13]
  ,[1,1,1,21]
  ,[1,2,4,35]
  ]
  *Pol_09> degree [13, 21, 35, 55, 81, 113, 151]
  2

  *Pol_09> genMatrix [-7,-2,15,50,109,198,323]
  [[1,0,0,0,-7]
  ,[1,1,1,1,-2]
  ,[1,2,4,8,15]
  ,[1,3,9,27,50]
  ]

The process of transforming the matrix to left triangular form is done by forward elimination: use one row to eliminate the first coefficient from the other rows by adjustment.

> adjustWith :: Row -> Row -> Row
> adjustWith (m:ms) (n:ns) = zipWith (-) (map (n*) ms) (map (m*) ns)

> echelon :: Matrix -> Matrix
> echelon rs
>   | null rs || null (head rs) = rs
>   | null rs   = map (0:) $ echelon $ map tail rs
>   | otherwise = piv : map (0:) (echelon rs')
>   where
>     rs' = map (adjustWith piv) (rs1 ++ rs3)
>     (rs1,rs2) = span leadZero rs
>     (piv:rs3) = rs2
>     leadZero (n:_) = n==0

  *> genMatrix [-7,-2,15,50,109,198,323]
  [[1,0,0,0,-7],[1,1,1,1,-2],[1,2,4,8,15],[1,3,9,27,50]]
  *Pol_09> echelon it
  [[1,0,0,0,-7]
  ,[0,-1,-1,-1,-5]
  ,[0,0,-2,-6,-12]
  ,[0,0,0,-12,-12]
  ]

Backward Gaussian elimination

An elimination step transforms a matrix in echelon form, minus its last row, a into a smaller matrix in echelon form.

> eliminate :: Rational -> Matrix -> Matrix
> eliminate p rs = map (simplify c a) rs
>   where
>     c = numerator p
>     a = denominator p
>     simplify c a row = init (init row') ++ [a*d - b*c]
>       where
>         d = last row
>         b = last $ init row
>         row' = map (*a) row

> backsubst :: Matrix -> [Rational]
> backsubst rs = backsubst' rs []
>   where
>     backsubst' [] ps = ps
>     backsubst' rs ps = backsubst' rs' (p:ps)
>       where
>         a   = (last rs) !! ((cols rs) -2)
>         c   = (last rs) !! ((cols rs) -1)
>         p   = c % a
>         rs' = eliminate p $ init rs

  *> backsubst [[1,0,0,0,-7]
                     ,[0,-1,-1,-1,-5]
                     ,[0,0,-2,-6,-12]
                     ,[0,0,0,-12,-12]
                     ]
  [(-7) % 1,1 % 1,3 % 1,1 % 1]

To use all this to analyze a polynomial sequence, generate the appropriate matrix (appropriate for the degree of the polynomial that we get from difference analysis of the sequence), put it in echelon form, and compute the values of the unknowns by backward substitution:

> solveSeq :: [Integer]  -- 
>          -> [Rational]
> solveSeq = backsubst . echelon . genMatrix

  *> solveSeq [0,1,5,14,30]
  [0 % 1,1 % 6,1 % 2,1 % 3]

  *> map (\ n -> (1/3)*n^3 + (1/2)*n^2 + (1/6)*n) [0..4]
  [0.0,0.9999999999999999,4.999999999999999,14.0,30.0]
  *> map ceiling it
  [0,1,5,14,30]
  *> solveSeq it
  [0 % 1,1 % 6,1 % 2,1 % 3]

Converter:

> -- p2fct :: Num a => [a] -> a -> a
> -- p2fct [] x = 0
> -- p2fct (a:as) x = a + (x* p2fct as x)

  *> [ n^3 + 5 * n^2 - 5 * n - 12 | n <- [0..9] ]
  [-12,-11,6,45,112,213,354,541,780,1077]
  *> map (p2fct [-12, -5, 5,1]) [0..9]
  [-12,-11,6,45,112,213,354,541,780,1077]

Exercise 9.6

  *> solveSeq [1,2,4,7,11]
  [1 % 1,1 % 2,1 % 2]

9.3 Polynomials and the Binomial Theorem

Theorem 9.7 (Newton's binomial theorem)

> choose n k = (product [(n-k+1)..n]) `div` (product [1..k])

Theorem 9.8 (Newton's binomial theorem, general version)

> choose' _ 0 = 1
> choose' n k
>   | n <  k = 0
>   | n == k = 1
>   | otherwise = choose' (n-1) (k-1) 
>               + choose' (n-1) k

Exercise 9.9
Which implementation is more efficient, choose or choose'?

choose is much more efficient than choose'.

Exercise 9.10
Derive the symmetry law for binomial coefficients
  choose n k = choose n (n-k)
directly from the definition.

Theorem 9.11 (Newton's binomial theorem again)

Exercise 9.12
Show that
  choose n k = (n `div` k) * choose (n-1) (k-1)

We get a more efficient function:

> binom _ 0 = 1
> binom n k
>   | n < k     = 0
>   | otherwise = (n * binom (n-1) (k-1)) `div` k

Exercise 9.13
Prove
  (choose n m) * (choose m k) == (choose n k) * (choose (n-k) (m-k))

Exercise 9.14

9.4 Polynomials for Combinatorial Reasoning
To implement the polynomial functions in a variable z, we'll represent a polynomial
  f z == f0 + f1*z + .. + fn*z^n
as a list of its coefficients:
  [f0, f1 .. fn]

Conventions
If f(z) is a polynomial (represented by z), then we use f for its coefficient list.
If this list f is non-empty, then the tail of f as f':
 f  == f0:f'
 f' == [f1 .. fn]
This convention yields 
  f(z) == f0 + z*f'(z)

The product of f and g looks like
  f(z)*g(z)
   == (f0 + f1*z + .. + fk*z^k)*(g0 + g1*z + .. + gm*z^m)
   == f0*g0 + (f0*g1 + f1*g0)*z + + (f0*g2 + f1*g1+ f2*g0)*z^2 + ..
   == f0*g0 + z * (f0*(g1 + g2*z + ..) + g0(f1 + f2*z + ..) + z f'(z)*g'(z))
   == f0*g0 + z * (f0*g'(z) + f'(z)*g(z))

Example 9.15

  *Pol_09> map ((z+1)^) [0..6]
  [[1]
  ,[1,1]
  ,[1,2,1]
  ,[1,3,3,1]
  ,[1,4,6,4,1]
  ,[1,5,10,10,5,1]
  ,[1,6,15,20,15,6,1]
  ]

Composition
The composition of polynomials f and g is also a polynomial.
  f(g(z)) == f0 + f1*(g(z))^1 + f2*(g(z))^2 + ..
          == f0 + g(z) * (f1 + f2*g(z) + f3*(g(z))^2 + ..)
          == f0 + g(z) * f'(g(z))

Example 9.16
We can use this to pcik an arbitrary layer in Pascal's triangle:

  *Pol_09> comp [1,1,1,1,1,1,1] [[0],[1,1]]
  [[1]
  ,[1,1]
  ,[1,2,1]
  ,[1,3,3,1]
  ,[1,4,6,4,1]
  ,[1,5,10,10,5,1]
  ,[1,6,15,20,15,6,1]
  ]

The close link between binomial coefficients and combinatorial notions makes polynomial reasoning a very useful tool for finding solutions to combinatorial problems.

Example 9.17
How many ways are there of selecting 10 red, blue or white marbles from a vase, in such a way that there are at least 2 of each color and at most five marbles have the same colour?

The answer is given by the coefficient of z^10 in the following polynomial
  (z^2 + z^3 + z^4 + z^5)^3

  *Pol_09> [0,0,1,1,1,1]^3
  [0,0,0,0,0,0,1,3,6,10,12,12,10,6,3,1]
  *Pol_09> it !! 10
  12

Notation
We associate coefficient lists with combinatorial problems by saying that
  [f0, .. , fn]
solves a combinatorial problem if fr (0 <= r <= n) gives the number of solutions for that problem.

Example 9.18
The polynomial solves the problem of picking r (0 <= r <= 10) elements from a set of 10.

  *Pol_09> (1+z)^10
  [1,10,45,120,210,252,210,120,45,10,1]

Q.E.D.

Example 9.19
Exercise 9.20
