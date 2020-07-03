quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = small ++ (x : big)
    where   small = quicksort (filter (<= x) xs)
            big = quicksort (filter (> x) xs)

lenNum :: (Integral a, Num b) => a -> b
lenNum e
    | e == 0 = 0
    | otherwise = 1 + lenNum (div e 10)

numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = [ read [i] | i <- (show n)]

isPandigital :: Integral a1 => [a1] -> Bool            
isPandigital x = (quicksort x == [1..9])

pandy = filter isPandigital [ numToList x ++ numToList (2*x) | x <- [9000..9999] ]
