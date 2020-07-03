fac n = product [2..n]

numToList :: (Integral a, Show a, Integral b, Read b) => a -> [b]
numToList n = reverse [ read [i] | i <- (show n)]

isCur n = (n == (sum . map fac . numToList) n)

t = (filter isCur [10..2540160])