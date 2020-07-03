quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = small ++ (x : big)
    where   small = quicksort (filter (<= x) xs)
            big = quicksort (filter (> x) xs)

sortedRemDup :: (Ord a) => [a] -> [a]
sortedRemDup x
    | length x < 2 = x
    | null (filter (/= h) x) = [h]
    | otherwise = h : (sortedRemDup xs)
    where   h = head x
            xs = drop ([ i | i <- [1..], x!!i /= h ]!!0) x

a = (length . sortedRemDup . quicksort) [ a^b | a <- [2..100], b <- [2..100] ]