val :: Int -> Int
val denom
    | denom == 1 = 1
    | (denom == 3 || denom == 6) = 5 * (div (val (denom-1)) 2)
    | otherwise = 2 * val (denom-1)

numWays :: Int -> Int
numWays cash = parCash cash 8
    where parCash cash denom
            | denom == 1 = 1
            | cash < val denom = parCash cash (denom-1)
            | cash == val denom = 1 + parCash cash (denom-1)
            | otherwise = sum [parCash (cash - i*(val denom)) (denom-1) | i <- [0..(div cash (val denom))]]