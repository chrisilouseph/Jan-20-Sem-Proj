numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = [ read [i] | i <- (show n)]

tenkStartChamp :: Integral p => p -> p
tenkStartChamp k
    | k == 0 = 1
    | otherwise = 9*k*10^(k-1) + tenkStartChamp (k-1)

nthDigit :: (Integral p, Read p) => Int -> p
nthDigit k = gap k 0
    where gap k j
            | tenkStartChamp (j+1) <= k = gap k (j+1)
            | tenkStartChamp j == k = 1
            | otherwise = (numToList y)!!(k-y')
            where   y = 10^j + div (k-tenkStartChamp j) (j+1)
                    y' = (j+1)*(y-10^j) + tenkStartChamp j

t = [ nthDigit (10^k) | k <- [0..6] ]