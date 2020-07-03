isPrime :: (Integral a) => a -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n < 2 = False
            | x > (floor . sqrt . fromIntegral) n = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

lenNum :: (Num a1, Show a2) => a2 -> a1
lenNum n = sum [ 1 | _ <- (show n)]

rotateNum :: (Integral a, Show a, Num t, Ord t) => a -> t -> a
rotateNum num tim
    | tim < 1 = num
    | otherwise = rotateNum newNum (tim-1)
    where newNum = (mod num 10) * (10^(lenNum num -1)) + div num 10

isCircNum :: (Show a, Integral a) => a -> Bool
isCircNum n = not ( False `elem` [ isPrime (rotateNum n t) | t <- [0..lenNum n] ])

t = filter isCircNum [2..999997]