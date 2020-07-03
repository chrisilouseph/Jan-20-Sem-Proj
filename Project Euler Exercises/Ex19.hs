isLeap :: Int -> Bool
isLeap x
    | mod x 4 > 0 = False
    | mod x 400 == 0 = True
    | mod x 100 == 0 = False
    | otherwise = True

daysInMonth :: Int -> Int -> Int
daysInMonth m y
    | ((m < 8 && odd m) || (m > 7 && even m)) = 31
    | m > 2 = 30
    | isLeap y = 29
    | otherwise = 28

firstSunOfMonth :: Int -> Int -> Int
firstSunOfMonth m y
    | y < 1901 && m == 1 = 7
    | m < 2 = mod (-daysInMonth 12 (y-1) + firstSunOfMonth 12 (y-1)) 7
    | otherwise = mod (-daysInMonth (m-1) y + firstSunOfMonth (m-1) y) 7

t = [ (m,y) | m <- [1..12], y <- [1901..2000], firstSunOfMonth m y == 1 ]