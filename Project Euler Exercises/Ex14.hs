collatzLen :: Integer -> Int
collatzLen n = length (seq n)
    where
        seq n
            | n < 1 = []
            | n == 1 = [1]
            | mod n 2 == 0 = n : seq (div n 2)
            | otherwise = n : seq (3*n+1)

maxCollatz :: Integer -> Int
maxCollatz lim = maximum (parSeq lim lim)
    where
        parSeq lim ind
            | lim < 1 = [-1]
            | ind < 0 = []
            | otherwise = collatzLen (ind) : parSeq lim (ind-1)
            
collatzLen' :: Int -> Integer
collatzLen' len = findn len 1
    where
        findn len n
            | len < 1 = -1
            | collatzLen n == len = n
            | otherwise = findn len (n+1)