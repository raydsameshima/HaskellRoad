COR_10.lhs

Chapter 10
Corecursion
Recursions without base case.

> module COR_10 where
>
> import System.Random (mkStdGen, randomRs)
> import Polynomials
> import PowerSeries

We'll show how non-deterministic processes can be viewed as functions from random integer streams to streams.

10.1 Corecersive Definitions
Infinite lists are often called streams.

> ones = 1 : ones
> nats = 0 : map (+1) nats
> odds = 1 : map (+2) odds

Exercise 10.1

> evens = 0 : map (+2) evens

Q.E.D.

Here are versions of the infinite lists above in terms of iterate:

> theOnes = iterate id 1
> theNats = iterate (+1) 0
> theOdds = iterate (+2) 1
>
> theEvens = iterate (+2) 0

Using zipWith,

> theNats1 = 0 : zipWith (+) ones theNats1
> theFibs = 0:1: zipWith (+) theFibs (tail theFibs)

The process on Fibonacci numbers that was defined Exercise 7.17 can be defined with corecursion:

> pr (x:ys@(y:z:zs)) = x*z-y*y : pr ys

The sieve of Eratosthenes also uses corecursion:

> sieve :: [Integer] -- [2..]
>       -> [Integer]
> sieve (0:ns) = sieve ns
> sieve (n:ns) = n : sieve (mark ns 1 n)
>   where
>     mark (y:ys) k m
>       | k == m    = 0 : (mark ys 1     m)
>       | otherwise = y : (mark ys (k+1) m)

Here is a faster way to implement the Sieve of Eratosthenes.
(rem in Haskell is relatively cheap.)

> sieve' :: Integral n => [n] -> [n]
> sieve' (n:ns) = n : sieve' (filter (\m -> (rem m n) /= 0) ns)
> primes' = sieve' [2..]

In this implementation, we actually remove multiples of x from the list on encounting x in the sieve'.
The property of NOT being a multiple of n is implemented by
  \m -> (rem m n) /= 0.

How does one prove that sieve and sieve' compute the same stream result for every stream argument?
Proof by induction does NOT work here, for there is no base case.

Exercise 10.3
The Thue-Morse sequence is a stream of 0's and 1's that is produced as follows.
  0
  01
  0110
  01101001
  0110100110010110

> tm 0 = 1
> tm 1 = 0
> 
> nextStep ns = ns ++ (map tm ns)
> thueMorse = iterate nextStep [0]

10.2 Processes and Labeled Transition Systems

A labeled transition system
  (Q,A,T)
consists of a set of state Q, a set of action labels A, and a ternary relation 
  T \subset (Q \times A \times Q)
the transition relation.
If (q,a,q') \in T, we write this as
  q \stackrel{a}{\to} q'.

Example 10.4
A model of a clock that ticks until it gets unhinged.
  c --tick--> c
  c --crack-> c0

    tick
   /    \
   \    /
    -->c--crack->c0

This process of the ticking clock is nondeterministic.
The clock keeps ticking, until at some point, for no reason, it gets stuck.
Nondeterministic behavior is determined by random factors, so a simple way of modeling nondeterminism is by modeling a process as a map from a randomly generated list of integers to a stream of actions.

> randomInts :: Int -- bound 
>            -> Int -- seed
>            -> [Int]
> randomInts b s = tail $ randomRs (0,b) $ mkStdGen s

Exercise 10.5
Note that
  randomInts 1 seed
generates a random stream of 0's and 1's.
In the long run, the proportion of 0's and 1's in such a stream will be 1 to 1.
How would you implement a generator for streams of 0' and 1's with, in the long run, a proportion of 0's and 1's of 2 to 1?

> random001 s = map (`mod` 2) $ randomInts 2 s

  *COR_10> let f s = length $ filter (==1) $ take 10000000 $ random001 s
  *COR_10> f 1
  3334403

We define a process as a map from streams of integers to streams of action labels.
To start a process, create an appropriate random integer stream and feed it to the process.

> type Process = [Int] -> [String]
> 
> start :: Process -> Int -> Int -> [String]
> start process bound seed = process $ randomInts bound seed

The clock process can now be modeled by means of the following corecursion:

> clock :: Process
> clock (0:xs) = "tick"  : clock xs
> clock (1:_ ) = "crack" : []

    tick
   /    \
   \    /
    -->*--crack-->*

  *COR_10> start clock 1 1
  ["tick","crack"]
  *COR_10> start clock 1 2
  ["crack"]
  *COR_10> start clock 1 3
  ["crack"]
  *COR_10> start clock 1 4
  ["tick","tick","crack"]
  *COR_10> start clock 1 25
  ["tick","tick","tick","tick","crack"]

Example 10.6
Consider a very simple vending machine that sells mineral water and beer.
Water costs one coin, beer two coins.

       ----moneyback------
      /                   \
     --beer-------\        \
    /              \        \
    -water-         \        \
   /       \         \        \
  v         \         \        \
  *--coin-->*--coin-->*--coin-->*

> vending, vending1, vending2, vending3 :: Process -- [Int] -> [String]
> vending  (0:xs) = "coin"      : vending1 xs
> vending  (1:xs) =               vending  xs
> vending1 (0:xs) = "coin"      : vending2 xs
> vending1 (1:xs) = "water"     : vending  xs
> vending2 (0:xs) = "coin"      : vending3 xs
> vending2 (1:xs) = "beer"      : vending  xs
> vending3 (0:xs) = "moneyback" : vending  xs
> vending3 (1:xs) =               vending3 xs

Example 10.7
A parking ticket dispenser works as follows.

> ptd :: Process
> ptd = ptd0 0
>
> ptd0 :: Int -> Process
> ptd0 0 (0:xs) = ptd0 0 xs
> ptd0 i (0:xs) = ("return " ++ show i ++ " euro") : ptd0 0 xs
> ptd0 i (1:xs) = "1 euro" : ptd0 (i+1) xs
> ptd0 i (2:xs) = "2 euro" : ptd0 (i+2) xs
> ptd0 0 (3:xs) = ptd0 0 xs
> ptd0 i (3:xs) = ("ticket " ++ show (i*20) ++ " min") : ptd0 0 xs

  *COR_10> take 6 $ start ptd 3 457
  ["2 euro","ticket 40 min","1 euro","ticket 20 min","1 euro","ticket 20 min"]

Example 10.8, 10.9, 10.10

The key question about processes is the question of identity: how does one prove that two processes are the same?

Before we end this brief introduction to processes we give a simple example of process interaction.

Example 10.11

How about a beer drinker who interacts with a vending machine?
It turns out that we can model this very elegantly as follows.

We let the user start with buying his/her first beer.
Next, we feed the stream of actions produced by the vending machine as input to the user, and the stream of actions produced by the user as input to the vending machine, and they keep each other busy.
This interaction can be modeled corecursively, as follows:

> actions   = user [0,0,1] responses
> responses = vending actions
>
> user acts ~(r:s:p:resps) = acts ++ user (proc [r,s,p]) resps
> proc ["coin", "coin", "beer"] = [0,0,1]

  *COR_10> take 8 actions 
  [0,0,1,0,0,1,0,0]
  *COR_10> take 8 responses 
  ["coin","coin","beer","coin","coin","beer","coin","coin"]

The user starts by inserting 2 coins and pressing the button, the machine responds with collecting the coins and issuing a can of beer, the user responds to this by inserting two more coins and pressing the button once more, and so on.

One hairy detail: the pattern
  ~(r:s:p:resps)
is a so-called lazy pattern.
Lazy pattern ALWAYS match, they are irrefutable.
This allows the initial request to be submitted "before" the list (r:s:p:resps) comes into existence by the response from the vending machine.


10.3 Proof by Approximation
One of the proof methods that work for corecursive programs is proof by approximation.

Domain
For this, we have to extend each data type to a so-called domain with a partial ordering
  \sqsubseteq
(the approximation order).
Every data type gets extended with an element
  \bot.
This is the lowest element in the approximation order.

Let 
  (D, \sqsubseteq)
be a partially ordered set, and let
  A \subset D.

An element x \in A is the greatest element of A iff \forall a \in A, a \sqsubseteq x.
Similarly, x is the least element of A iff \forall a \in A, x \sqsubseteq a.

Note that there are D with A \subset D for which such least and greatest elements do not exist.

Exercise 10.12

An element x \in D is an upper bound of A iff \forall a \in A, a \sqsubseteq x.
Use
  A^u := {x \in D | \forall a \in A, a \sqsubseteq x}
for the set of all upper bounds of A.
Similarly, x \in D is a lower bound of A iff \forall a \in A, x \sqsubseteq a, and
  A^l := {x \in D | \forall a \in A, x \sqsubseteq a}

An element x \in D is the least upper bound(lub) of A iff x is the least element of A^u.
The least upper bound is also called the supremum of A.

E.g., consider (R, <=).
Take
  A := { n/(n+1) | n \in N} \subset R
Then
  A := {0,1/2, 2/3, 3/4, .. }
and
  A^u = {r \in R | r >= 1}
The least upper bound of A is clearly 1.



