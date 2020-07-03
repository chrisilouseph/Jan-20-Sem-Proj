fac :: Integer -> Integer
fac n = product [1..n]

t = div ((fac 40)  (fac 20)^2)