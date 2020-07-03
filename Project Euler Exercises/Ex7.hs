isPrime :: Integer -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n == 1 = False
            | n == x = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

prime :: Integer -> Integer -> Integer
prime f j
    | f < 1 = -1
    | not (isPrime j) = prime f (j+1)
    | f == 1 = j
    | otherwise = prime (f-1) (j+1)

nthPrime :: Integer -> Integer
nthPrime n = prime n 1
        