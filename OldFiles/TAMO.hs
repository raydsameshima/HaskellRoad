-- chapter 2

module TAMO

where

-- if, then
infix 1 ==>
(==>) :: Bool -> Bool -> Bool
x ==> y = (not x) || y
{- -- or we can define more explicitly, like a truth table
True  ==> x = x
False ==> x = True
-}

-- equivalence
infix 1 <=>
(<=>) :: Bool -> Bool -> Bool
x <=> y = x == y

infixr 2 <+>
(<+>) :: Bool -> Bool -> Bool
x <+> y = x /= y

p0 = True -- gloabal variables??
q0 = False
formula1 = (not p0) && (p0 ==> q0) <=> not (q0 && (not p0))
formula2 p0 q0 = ((not p0) && (p0 ==> q0) <=> not (q0 && (not p0)))

valid1 :: (Bool -> Bool) -> Bool
valid1 bf = (bf True) && (bf False)

excluded_middle :: Bool -> Bool
excluded_middle p = p || not p

valid2 :: (Bool -> Bool -> Bool) -> Bool
valid2 bf = (bf True True)
           && (bf True False)
           && (bf False True)
           && (bf False False)

form1 p q = p ==> (q ==> p)
form2 p q = (p ==> q) ==> p

valid3 :: (Bool -> Bool -> Bool -> Bool) -> Bool
valid3 bf = 
 and [bf p q r | p <- [True, False],
                 q <- [True, False], 
                 r <- [True, False]] 

valid4 :: (Bool -> Bool -> Bool -> Bool -> Bool) -> Bool
valid4 bf = 
 and [bf p q r s | p <- [True, False], 
                   q <- [True, False], 
                   r <- [True, False], 
                   s <- [True, False]] 

logEquiv1 :: (Bool -> Bool) -> (Bool -> Bool) -> Bool
logEquiv1 bf1 bf2 =
 (bf1 True <=> bf2 True) && (bf1 False <=> bf2 False)

logEquiv2 :: (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> Bool
logEquiv2 bf1 bf2 =
 and [(bf1 p q) <=> (bf2 p q) | p <- [True, False], 
                                q <- [True, False]]

logEquiv3 :: (Bool -> Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool -> Bool) -> Bool
logEquiv3 bf1 bf2 =
 and [(bf1 p q r) <=> (bf2 p q r) | p <- [True, False], 
                                    q <- [True, False], 
                                    r <- [True, False]]

formula3 p q = p
formula4 p q = (p <+> q) <+> q
-- logEquiv2 formula3 formula4

-- double negation
doubleNegate :: Bool -> Bool
doubleNegate p = not . not $ p

-- contraposition
ifThen :: Bool -> Bool -> Bool
ifThen p q = p ==> q
contraposition :: Bool -> Bool -> Bool
contraposition p q = (not q) ==> (not p)

theorem2_12_2 :: Bool -> Bool
theorem2_12_2 p = p ==> False
check_therem2_12_2 = logEquiv1 theorem2_12_2 not

lex2_20_1 :: Bool -> Bool -> Bool
rex2_20_1 :: Bool -> Bool -> Bool
lex2_20_1 p q = (not p) ==> q
rex2_20_1 p q = p ==> (not q) 
ex2_20_1 = lex2_20_1 `logEquiv2` rex2_20_1

lex2_20_4 p q r = p ==> (q ==> r)
rex2_20_4 p q r = q ==> (p ==> r)
ex2_20_4 = lex2_20_4 `logEquiv3` rex2_20_4

ex2_20_5 = l `logEquiv3` r
 where
  l p q r = p ==> (q ==> r)
  r p q r = (p ==> q) == r

ex2_20_6 = l `logEquiv2` r
 where
  l p q = (p ==> q) ==> p
  r p q = p

solveQdr :: (Float, Float, Float) -> (Float, Float)
solveQdr = \ (a, b, c) -> if a == 0 then error "not quadratic"
                          else let d = b^2 - 4 * a * c in
                          if d < 0 then error "no real solutions"
                          else ((-b + sqrt d) / 2*a, (-b - sqrt d) / 2*a)

-- forall, exists
every, some :: [a] -> (a -> Bool) -> Bool
every xs p = all p xs
some xs p = any p xs

page70_1 = every [1,4,9] (\ x -> some [1,2,3] (\ y -> x == y^2))
page70_2 = all (\ x -> any (\ y -> x == y^2) [1,2,3]) [1,4,9]

unique :: (a -> Bool) -> [a] -> Bool
unique p xs = length (filter p xs) == 1

test1 = logEquiv1 id (\ p -> not (not p))
