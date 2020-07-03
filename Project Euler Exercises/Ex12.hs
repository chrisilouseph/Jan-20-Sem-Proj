numDiv :: Integer -> Integer
numDiv n = parDiv n 2
    where 
        parDiv n k
            | n < 1 = -1
            | n == 1 = 1
            | 2 * k > n = 2
            | otherwise = parDiv n (k+1) + if mod n k == 0 then 1 else 0

firstDiv :: [Integer] -> Integer -> Integer
firstDiv a n = most a n 0
    where
        most a n c
            | a == [] = -1
            | n < 1 = -1
            | numDiv (a!!c) > n = a!!c
            | otherwise = most a n (c+1)

t = [ div (n*(n+1)) 2 | n <- [1..] ]
f = firstDiv t 500