import Data.List (intersperse,concat)

numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = reverse [ read [i] | i <- (show n)]

smallRootFrac xs = parFrac $ reverse $ 1 : (intersperse 1 xs)
    where   parFrac [x,y] = (y,x)
            parFrac list = parFrac $ ((list!!0)*(list!!2)+list!!1) : ((list!!0)*(list!!3)) : (drop 4 list)

rootFrac xs = ((snd p)*(head xs) + (fst p), snd p)
    where p = smallRootFrac (drop 1 xs)

e = 2:1:2:(concat [[1,1,k] | k <- [4,6..]])