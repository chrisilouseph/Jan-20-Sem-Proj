numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = [ read [i] | i <- (show n)]

lenNum :: (Integral a, Num b) => a -> b
lenNum e
    | e == 0 = 0
    | otherwise = 1 + lenNum (div e 10)

quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = small ++ (x : big)
    where   small = quicksort (filter (<= x) xs)
            big = quicksort (filter (> x) xs)

isPandigital x = (quicksort x == [1..9])

s = [ (a,b) | a <- [2..1962], b <- (a' a) ]
    where a' a = [ x | x <- [a+1..1963], not (True `elem` ([i `elem` numToList x | i <- numToList a])) ]

s' = [ (a,b) | (a,b) <- s, isPandigital (numToList a ++ numToList b ++ numToList (a*b)) ]