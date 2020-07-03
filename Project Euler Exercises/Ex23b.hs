isAbund :: Integral a => a -> Bool
isAbund n = fac n 2 0
    where fac n x s
            | s > n = True
            | mod n x == 0 = fac n (x+1) (x + (div n x) + s)
            | x^2 > n = ((s + 1) > n)
            | x^2 == n = (s+x+1 > n) 
            | otherwise = fac n (x+1) s

abund = 12 : filter isAbund [13..28111]

reqSum = sum [1..23] + parSum 25 0
    where parSum j check
            | j > 28123 = 0
            | abund!!check > (div j 2) = j + parSum (j+1) 0
            | isAbund (j - (abund!!check)) = parSum (j+1) 0
            | otherwise = parSum j (check+1)