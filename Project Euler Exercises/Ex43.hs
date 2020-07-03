primes = [2,3,5,7,11,13,17]

pandigital 1 = [1]
pandigital n = [ (x - cut)*10 + n*10^i + cut | x <- pandigital (n-1), i <- [0..(n-1)], let cut = mod x (10^i) ]

pandigital0 1 = [10]
pandigital0 n = [(x - cut)*10 + n*10^i + cut | x <- pandigital0 (n-1), i <- [0..n], let cut = mod x (10^i) ] ++ [n*10^n + x | x <- pandigital (n-1)]

primeDiv :: Integer -> Bool
primeDiv a = ([mod (mod (div a (10^(6-i))) 1000) (primes!!i) | i <- [0..6]] == replicate 7 0)