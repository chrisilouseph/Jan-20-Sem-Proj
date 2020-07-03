isPrime :: Integer -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n == 1 = False
            | n == x = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

sumPrimes :: Integer -> Integer
sumPrimes 2 = 2
sumPrimes n = sumPrimes (n-1) + if isPrime n then n else 0