isPrime :: (Integral a) => a -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n < 2 = False
            | x > (floor . sqrt . fromIntegral) n = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

lenNum :: (Show a, Integral b) => a -> b
lenNum n = sum [ 1 | _ <- (show n)]


isLeftTruncPrime x
    | not (isPrime x) = False
    | x < 10 = True
    | otherwise = isLeftTruncPrime (mod x (10^(lenNum x -1)))


isRightTruncPrime x
    | not (isPrime x) = False
    | x < 10 = True
    | otherwise = isRightTruncPrime (div x 10)


isTruncPrime x = isRightTruncPrime x && isLeftTruncPrime x

t = take 10 (filter isTruncPrime [23..])