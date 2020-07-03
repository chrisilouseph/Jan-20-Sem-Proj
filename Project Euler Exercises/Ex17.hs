lenNum :: Integer -> Int
lenNum x
    | x == 17 = 9
    | x == 100 = 10
    | x == 1000 = 11
    | (x <= 2 || x == 6 || x == 10) = 3
    | (x == 4 || x == 5 || x == 9) = 4
    | (x == 15 || x == 16 || x == 70) = 7
    | (x == 13 || x == 14 || x == 18 || x == 19) = 8
    | (x == 3 || x == 7 || x == 8 || x == 40 || x == 50 || x == 60) = 5
    | (x == 11 || x == 12 || x == 20 || x == 30 || x == 80 || x == 90) = 6
    | x > 100 = lenNum (div x 100) + 7 + if mod x 100 == 0 then 0 else (3 + lenNum (mod x 100))
    | otherwise = lenNum (x - mod x 10) + lenNum (mod x 10)

sumLen :: Integer -> Int
sumLen n = sum [ lenNum x | x <- [1..n] ]