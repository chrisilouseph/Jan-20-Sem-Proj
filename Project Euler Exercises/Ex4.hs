numToList :: Integer -> [Integer]
numToList n = parList n []
    where
        parList n f
            | n < 0 = [-1]
            | n > 0 = parList (div (n - (mod n 10)) 10) (f++[mod n 10])
            | f == [] = [0]
            | otherwise = f

isPal :: Integer -> Bool
isPal n = (numToList n == reverse (numToList n))

m = maximum [ x*y | x <- [100..999], y <- [100..999], isPal (x*y) ]