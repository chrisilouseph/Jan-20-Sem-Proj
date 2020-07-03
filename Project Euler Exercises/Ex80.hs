lenNum :: (Show a, Num b) => a -> b
lenNum n = sum [1 | i <- (show n)]

isqrt = floor.sqrt.fromIntegral

sqrt' n p = parRoot n p (isqrt n)
    where parRoot n x p
            | x >= 10^p = x
            | otherwise = parRoot n p $ last $ takeWhile cond [x*10 + k | k <- [0..9]]
            where cond s = s^2 < n * 100 ^ (lenNum s)