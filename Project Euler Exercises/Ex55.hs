numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = [read [i] | i <- (show n)]

isPal :: (Show a, Integral a) => a -> Bool
isPal x = (numToList x == reverse (numToList x))

numChar :: (Eq t, Num t) => t -> Char
numChar 0 = '0'
numChar x = succ (numChar (x-1))

numPal :: (Show a, Integral a) => a -> Integer
numPal n = read (map numChar (reverse (numToList n)))

isLychrel :: Integer -> Bool
isLychrel n = parCheck n 0
    where parCheck n itNum
            | itNum >= 50 = True
            | isPal (n + (numPal n)) = False
            | otherwise = parCheck (n + (numPal n)) (itNum+1)