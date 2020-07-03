import Data.List (delete)

numToList :: Show a => a -> [Char]
numToList n = [ i | i <- (show n)]

perms :: Integer -> [Integer]
perms k = map r (permsL (numToList k))
    where   permsL :: Eq a => [a] -> [[a]]
            permsL [x] = [[x]]
            permsL a = [k:p | k <- a, p <- permsL (delete k a)]
            r x = read x :: Integer

isCube :: Integral a => a -> Bool
isCube i = (i == ((^3). floor. (** (1/3)). fromIntegral) i)

t = takeWhile (/= 5) $ map cond [5..]
    where cond k = length $ filter (== True) $ map isCube $ perms (k^3)