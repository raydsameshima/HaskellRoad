module PowerSeries 

where 

import Polynomials 

default (Integer, Rational, Double) 
-- The default for the display of fractional numbers in Haskell is floating point notation.
-- As we are going to develop streams of integers and streams of fractions in this chapter, it is convenient to have them displayed with unlimited precision in integer or rational notation.

instance (Ord a, Fractional a) => Fractional [a] where
  fromRational c  = [fromRational c] 
  fs     / []     = error "division by 0 attempted"
  []     / gs     = []
  (0:fs) / (0:gs) = fs / gs 
  (_:fs) / (0:gs) = error "division by 0 attempted"
  (f:fs) / (g:gs) = let q = f/g in 
       q : (fs - q.*gs) / (g:gs)

int :: Fractional a => [a] -> [a]
int fs = 0 : int1 fs 1 where 
  int1 []     _ = []
  int1 (g:gs) n = g/n : (int1 gs (n+1))

expz = 1 + (int expz) 
