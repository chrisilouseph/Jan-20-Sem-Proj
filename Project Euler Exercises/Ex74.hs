numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = [ read [i] | i <- (show n)]

fac :: (Ord p, Num p) => p -> p
fac x = if x < 2 then 1 else x * fac (x-1)

nextNum :: (Show a1, Integral a1, Integral a2, Read a2) => a1 -> a2
nextNum x = sum $ map fac $ numToList x

chain :: (Show a, Integral a, Read a) => a -> [a]
chain s = parChain [s]
    where parChain xs
            | n `elem` xs = xs
            | otherwise = parChain (n:xs)
            where n = nextNum (head xs)