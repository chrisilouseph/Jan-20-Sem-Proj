mSum :: Integer -> Integer
mSum 1 = 0
mSum x = mSum (x-1) + if (mod x 3 == 0 || mod x 5 == 0) then x else 0