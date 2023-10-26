module LFPLIter where

iter :: Integer -> Integer -> Integer
iter 0 _ = 1
iter k 0 = 0
iter k n = iter (k-1) (n-1) + iter k (n-1)

binom :: Integer -> Integer -> Integer
binom k n = product [1..n] `div` (product [1..k] * product [1..n-k])
