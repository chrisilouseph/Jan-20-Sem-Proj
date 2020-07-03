isPrime :: (Integral a) => a -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n < 2 = False
            | x > (floor . sqrt . fromIntegral) n = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

isGold n = parGold n 1
    where parGold n check
            | n < 3 + s = True
            | isPrime (n-s) = False
            | otherwise = parGold n (check+1)
            where s = 2*(check^2)

oddComp = [ x | x <- [35..], odd x, not (isPrime x) ]
t = (filter isGold oddComp)