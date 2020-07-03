numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = [ read [i] | i <- (show n)]

decToBin :: (Integral a) => a -> a
decToBin n
    | n == 0 = 0
    | even n = 10 * decToBin (div n 2)
    | otherwise = 1 + decToBin (n-1)

t = filter req [1..999999]
    where req x = (reverse (numToList x) == numToList x) && ( numToList (decToBin x) == (reverse . numToList . decToBin) x)