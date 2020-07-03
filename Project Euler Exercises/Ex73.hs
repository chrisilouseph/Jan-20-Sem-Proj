cop :: Integral a => a -> a -> Bool
cop a b = (1 == ordHcf b a)
    where ordHcf x y
            | mod y x == 0 = x
            | otherwise = ordHcf (mod y x) x

more3 :: Integral a => a -> a
more3 d = 1 + floor (fromIntegral d/fromIntegral 3)

less2 :: Integral a => a -> a
less2 d = if odd d then div d 2 else div d 2 -1

req k = sum [length (filter (cop d) [more3 d..less2 d]) | d <- [5..k]]