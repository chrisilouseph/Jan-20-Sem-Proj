isqrt :: (Integral c, Integral a) => a -> c
isqrt x = (floor . sqrt . fromIntegral) x

isPrime :: (Integral a) => a -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n < 2 = False
            | x > isqrt n = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

numPrimes :: (Integral a) => a -> a -> a
numPrimes a b = [ n | n <- [0..], not (isPrime (n^2 + a*n + b)) ]!!0

primeList = [ numPrimes a b | b <- (filter isPrime [2..1000]), a <- [-2*(isqrt b)..2*(isqrt b)] ]

prodList = [ a*b | b <- (filter isPrime [2..1000]), a <- [-2*(isqrt b)..2*(isqrt b)] ]

i = [ x | x <- [0..], primeList!!x == 71 ]!!0