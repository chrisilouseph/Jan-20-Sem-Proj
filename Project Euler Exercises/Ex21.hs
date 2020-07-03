sumDiv :: Int -> Int
sumDiv n = sum [ k | k <- [1..(div n 2)], mod n k == 0 ]

amicableSum :: Int -> Int
amicableSum n = sum [ k | k <- [1..n], k /= sumDiv k, sumDiv (sumDiv k) == k ]