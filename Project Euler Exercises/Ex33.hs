sortedRemDup :: (Ord a) => [a] -> [a]
sortedRemDup x
    | length x < 2 = x
    | null (filter (/= h) x) = [h]
    | otherwise = h : (sortedRemDup xs)
    where   h = head x
            xs = drop ([ i | i <- [1..], x!!i /= h ]!!0) x

s = [ x | x <- [11..99], mod x 10 > 0]

lTrunc n = mod n 10
rTrunc n = div n 10

t'' = [ (a,b,c,d) | a <- s, b <- (filter (> a) s), c <- [lTrunc a], d <- [rTrunc b], a*d == b*c ]
u'' = [ (a,b,c,d) | a <- s, b <- (filter (> a) s), c <- [rTrunc a], d <- [lTrunc b], a*d == b*c ]

t' = [ (a,b,c,d) | (a,b,c,d) <- t'', (mod b 11 > 0 || mod a 11 > 0 ) ]
u' = [ (a,b,c,d) | (a,b,c,d) <- u'', (mod b 11 > 0 || mod a 11 > 0 ) ]

t = sortedRemDup [(a,b) | (a,b,c,d) <- t']