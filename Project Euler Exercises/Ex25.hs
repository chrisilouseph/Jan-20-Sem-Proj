fib :: Integer -> Integer
fib n = round (((1.0 + sqrt 5.0)/2)^n/sqrt 5.0)

numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = reverse [ read [i] | i <- (show n)]

nDigitFib :: Integer -> Integer
nDigitFib n = [ x | x <- [18..],  (floor . logBase 10.0 . fromIntegral . fib) x == 1000 ]!!0