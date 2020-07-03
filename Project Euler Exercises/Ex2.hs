fibSum :: Int -> Int
fibSum 1 = 0
fibSum x = fibSum (x-1) + if (checkFib' x 1 && mod x 2 == 0) then x else 0

fib :: Int -> Int
fib 1 = 1
fib 2 = 2
fib n = fib (n-1) + fib (n-2)

checkFib' :: Int -> Int -> Bool
checkFib' x n
    | x == fib n = True
    | x < fib n = False
    | otherwise = checkFib' x (n+1)

fibSum' :: Int -> Int -> Int
fibSum' x 1 = 0
fibSum' x n = fibSum' x (n-1) + if (fib n <= x && mod (fib n) 2 == 0) then fib n else 0