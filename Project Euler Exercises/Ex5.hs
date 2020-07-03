bigPower :: Integer -> Integer -> Integer
bigPower s l
    | s < 2 = -1
    | s > l = 0
    | otherwise = 1 + bigPower s (div l s)

isPrime :: Integer -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n == 1 = False
            | n == x = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

smallMul :: Integer -> Integer
smallMul n = prod n 2
    where
        prod x y
            | x < 2 = -1
            | y > x = 1
            | isPrime y = (prod x (y+1)) * y^(bigPower y x)
            | otherwise = prod x (y+1)