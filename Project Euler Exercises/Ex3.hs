isPrime :: Int -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n == 1 = False
            | n == x = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

smallPrime :: Int -> Int
smallPrime n = fac n 2
    where
        fac n x
            | n == 1 = -1
            | n == x = n
            | mod n x == 0 = x
            | otherwise = fac n (x+1)

bigPrime :: Int -> Int
bigPrime n
    | n == 1 = -1
    | isPrime n = n
    | otherwise = bigPrime (div n (smallPrime n))
