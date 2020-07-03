import Data.List (delete)

isPrime :: (Integral a) => a -> Bool
isPrime n = fac n 2
    where fac n x
            | n < 2 = False
            | x^2 > n = True
            | mod n x == 0 = False
            | otherwise = fac n (x+1)

prop a b = isPrime (read (show (allPrimes!!a) ++ show (allPrimes!!b)) :: Integer)
propf xs = and [prop x y | x <- xs, y <- delete x xs]

allPrimes = filter isPrime [3..]

primes 2 = [[a,b] | a <- [1..], b <- [0..a-1], propf [a,b]]
primes i = [k:s | k <- [head s +1..], s <- primes (i-1), propf (k:s)]
-- samSpace = [[(primes 1)!!a, primes!!b, primes!!c, primes!!d] | a <- [3..], b <- [0..a-1], c <- [0..b-1], d <- [0..c-1]]
-- t = takeWhile (not.propf) samSpace
