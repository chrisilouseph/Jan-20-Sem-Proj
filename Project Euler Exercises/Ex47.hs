smallPrimePower :: (Integral t, Integral b) => t -> (t, b)
smallPrimePower n = fac n 2
    where fac n x
            | n < 2 = (-1,-1)
            | x > (floor . sqrt . fromIntegral) n = (n,1)
            | mod n x == 0 = (x, head [p-1 | p <- [1..], mod n (x^p) > 0])
            | otherwise = fac n (x+1)

distPrimeDiv :: (Integral a, Num b) => a -> b
distPrimeDiv n
    | n < 2 = 0
    | otherwise = 1 + (distPrimeDiv (div n (p^e)))
    where (p,e) = smallPrimePower n

firstCons :: Int -> Int
firstCons n = parCons n 2
    where parCons n check
            | n < 1 = 0
            | [distPrimeDiv (check+i)| i <- [0..(n-1)]] == replicate n n = check
            | otherwise = parCons n (check+1)