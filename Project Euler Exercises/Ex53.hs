c n r = div (product [(r+1)..n]) (product [1..(n-r)])

reqCount = parCount 23 0
    where parCount n r
            | n > 100 = 0
            | r > n = parCount (n+1) 0
            | c n r > 10^6 = 1 + parCount n (r+1)
            | otherwise = parCount n (r+1)