pent n = div (n*(3*n-1)) 2

inPent n = if (div (n'*(3*n'-1)) 2 == n) then n' else (-1)
    where n' = div (1 + (floor.sqrt.fromIntegral) (1+24*n)) 6

hex n =  n*(2*n-1)

t' = [k | k <- [143..], inPent (hex k) > 0]