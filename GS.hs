-- chapter 01 

module GS where

--prime.hs
-- rem = remainder つまり余りがあるかないかで真偽返す
-- rem :: Integral a => a -> a -> a
divides :: Integer -> Integer -> Bool
divides d n = (rem n d == 0)
-- ld n is the least (the smallest) diviser of n.
-- If ld n is not a prime, then there exists p,q < n with (ld n) = p*q.
-- Now we have p and q are divisor of n and they are smaller than (ld n).
-- This cntradict the smallest assumption.
-- Thus ld n is prime.
ld :: Integer -> Integer
ld n = ldf 2 n
-- ldf k n はk<n がkの約数であるかどうかを調べる
-- 実はkは刻みが1なので非効率、後ほど改良する
ldf :: Integer -> Integer -> Integer
ldf k n 
 | divides k n = k
 | k^2 > n     = n -- この判定条件がミソ、高々平方根までで充分
 | otherwise   = ldf (k+1) n -- ただし刻みは一ずつ 
-- isPrime の方が名前合ってる
prime0 :: Integer -> Bool
prime0 n 
 | n <  1    = error "not a positive integer"
 | n == 1    = False
 | otherwise = (ld n == n) -- 最小の約数が自身であれば素数でしょう
-- 約数のリストを返します
factors :: Integer -> [Integer]
factors n 
 | n <  1    = error "argument not positive"
 | n == 1    = []
 | otherwise = p : factors (div n p) 
  where p = ld n -- p はn の（最小の）約数なのでn はp で必ず割り切れる

-- improved versions
-- ldp は多分広義の意味で再帰になっているのかな？
ldp :: Integer -> Integer
ldp n = ldpf primes1 n
-- 素数のリストからdivisor を探してあればそれを、なければ自身を返す、すなわち不動点(ldpf p = p)は素数
ldpf :: [Integer] -> Integer -> Integer
ldpf (p:ps) n -- ここで(p:ps) は素数のリストを想定、後で用意する 
 | rem n p == 0 = p
 | p^2 >n       = n
 | otherwise    = ldpf ps n 
-- 素数のリスト、奇数列から素数判定でフィルター
primes1 :: [Integer]
primes1 = 2 : filter prime [3,5..]
-- 素数判定、やっぱり名前はisPrime のほうが良いな
prime :: Integer -> Bool
prime n 
 | n < 1     = error "not a positive integer"
 | n == 1    = False
 | otherwise = ldp n == n

-- minMax.hs
mnmInt :: [Int] -> Int
mnmInt []     = error "empty list"
mnmInt [x]    = x
mnmInt (x:xs) = min x (mnmInt xs)

maxInt :: [Int] -> Int
maxInt []     = error "empty list"
maxInt [x]    = x
maxInt (x:xs) = max x (maxInt xs)

-- srtString.hs
-- quick sort
srtString :: [String] -> [String]
srtString [] = []
srtString (x:xs) = before ++ (x : after)
 where
  before = srtString $ filter (< x) xs  
  after  = srtString $ filter (>= x) xs

-- average.hs
average :: [Int] -> Float
average [] = error "empty list"
average lst = fromIntegral (sum lst) / fromIntegral n
-- where n = fst . last . zip [1..] $ lst
 where n = length lst

-- myCount.hs
{-
myCount :: Char -> [Char] -> Int
myCount _ [] = 0
myCount w (x:xs) | w == x    = 1 + (myCount w xs)
		 | otherwise = myCount w xs
-}
myCount :: Char -> [Char] -> Int
myCount w lst = myCount' w lst 0 
 where 
  myCount' _ [] ans = ans
  myCount' w (x:xs) ans 
   | w == x    = myCount' w xs (ans + 1)
   | otherwise = myCount' w xs ans

-- blowup.hs
blowup :: [Char] -> [Char]
blowup (x:xs) = blowup' (x:xs) 1 
 where 
  blowup' []     _ = []
  blowup' (x:xs) n = replicate n x ++ blowup' xs (n+1)

-- prefix.hs
prefix :: String -> String -> Bool
prefix [] _ = True
prefix _ [] = False
prefix (x:xs) (y:ys) = (x==y) && prefix xs ys

substring :: String -> String -> Bool
substring [] _ = True
substring _ [] = False
substring (x:xs) (y:ys) =
 ((x==y) && (prefix xs ys)) || (substring (x:xs) ys)

sum' :: [Int] -> Int
--sum' [x] = x
sum' [] = 0
sum' (x:xs) = x + sum' xs
