quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = small ++ (x : big)
    where   small = quicksort (filter (<= x) xs)
            big = quicksort (filter (> x) xs)

numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = reverse [ read [i] | i <- (show n)]

lenNum :: (Integral a, Num b) => a -> b
lenNum e
    | e == 0 = 0
    | otherwise = 1 + lenNum (div e 10)

arePerm a b = ((quicksort . numToList) a == (quicksort . numToList) b)

samSpace = [n | n <- [1..], n <= floor (10^(lenNum n)/6) ]

perm :: Integer -> [Integer]
perm 6 = [x | x <- samSpace, arePerm x (6*x)]
perm n = [x | x <- perm (n+1), arePerm x (n*x)]