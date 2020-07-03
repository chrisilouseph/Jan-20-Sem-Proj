rootExp :: Int -> [Int]
rootExp n = if d == 0 then [sn] else [sn,f] ++ (parList n (f*d-sn) d)
    where   sn = (floor.sqrt.fromIntegral) n
            d = n-sn^2
            f = floor $ ((sqrt.fromIntegral) n + fromIntegral sn)/fromIntegral d
            parList n k num
                | k == sn && num == 1 = []
                | otherwise = w : (parList n k' num')
                where   num' = div (n-k^2) num
                        w = floor $ ((sqrt.fromIntegral) n + fromIntegral k)/fromIntegral num'
                        k' = w*num' - k

t = length $ filter (== True) $ map (even. length. rootExp) [2..9999]