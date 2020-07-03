isPrime :: (Integral a) => a -> Bool
isPrime n = fac n 2
    where
        fac n x
            | n < 2 = False
            | x > (floor . sqrt . fromIntegral) n = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = reverse [ read [i] | i <- (show n)]

quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = small ++ (x : big)
    where   small = quicksort (filter (<= x) xs)
            big = quicksort (filter (> x) xs)

arePerm a b = ((quicksort . numToList) a == (quicksort . numToList) b)

primes = filter isPrime [1001..9999]

permPrimes = [[a,b,c] | a <- primes, let permA = filter (arePerm a) [1001..9999], b <- filter (>a) permA, c <- filter (>b) permA, isPrime b, isPrime c]

apPermPrimes = [x | x <- permPrimes, x!!0 + x!!2 == 2*(x!!1)]