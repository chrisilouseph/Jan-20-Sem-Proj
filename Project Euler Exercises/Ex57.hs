nthExp :: (Eq a1, Num a1, Num a2, Num b) => a1 -> (a2, b)
nthExp n = (fst (parExp n) + snd (parExp n), snd (parExp n))
    where parExp x
            | x == 1 = (1,2)
            | otherwise = (snd prev, fst prev + 2*(snd prev))
            where prev = parExp (x-1)

lenNum :: Show a => a -> Int
lenNum n = length [ 1 | i <- (show n)]

t = [nthExp x | x <- [1..1000], (lenNum . fst . nthExp) x > (lenNum . snd . nthExp) x]