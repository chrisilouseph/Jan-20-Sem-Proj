pent = [ div (n*(3*n-1)) 2 | n <- [1..] ]
-- 3n2-n-2y=0
-- n=1+|1+24y/6
isInPent x = (div (n*(3*n-1)) 2 == x)
    where n = div (1 + (floor.sqrt.fromIntegral) (1+24*x)) 6

sumPent = [ (b,a) | a <- [1..], b <- [a-1,a-2..0], let s = pent!!a + pent!!b, isInPent s]
req = [ (b,a) | (b,a) <- sumPent, let d = pent!!a - pent!!b, isInPent d]

try = 5482660

minD = firstNum 1 0
    where firstNum num check
            | check == num = firstNum (num+1) num