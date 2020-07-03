numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = reverse [ read [i] | i <- (show n)]

t :: (Integral a, Show a, Read a) => a -> [a]
t n = [ x | x <- [2..n], x == sum (map (^5) (numToList x)) ]