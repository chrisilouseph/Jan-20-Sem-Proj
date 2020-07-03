import Data.List (group,(\\),sort)

close37 :: Integral a => a -> a
close37 d = (`div` 7) $ last $ takeWhile (< d*3) $ [7 *(div (3*d) 7)-1..]

posSet = [(close37 den,den) | den <- [500000..10^6]]

remSmall = group' posSet
    where group' a
            | null a = []
            | otherwise = (head s) : group' (a \\ s)
            where s = take (length (head (group (map fst a)))) a

reqDec = last $ sort $ map (\(a,b) -> (fromIntegral a)/(fromIntegral b)) remSmall -- == 0.42857128571385716

t = fst $ head [(a,b) | (a,b) <- posSet, (fromIntegral a)/(fromIntegral b) > 0.4285712857138571 ]