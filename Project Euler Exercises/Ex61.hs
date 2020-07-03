import Data.List ((\\))

p :: (Integral a1, Num a2, Eq a2) => a2 -> a1 -> a1
p x n = case x of   3 -> div (n^2+n) 2
                    4 -> n^2
                    5 -> div (3*n^2-n) 2
                    6 -> 2*n^2-n
                    7 -> div (5*n^2-3*n) 2
                    8 -> 3*n^2-2*n

isCyclic :: Integral a => a -> a -> Bool
isCyclic f s = (mod f 100 == div s 100)

pSet :: (Integral a1, Num a2, Eq a2) => a2 -> [a1]
pSet x = (filter f. takeWhile (< 10^4). dropWhile (< 1010). map (p x)) [1..]
    where f n = (mod (div n 10) 10) > 0 -- 3rd digit not zero

c :: (Integral a1, Num t, Num a2, Eq t, Eq a2, Enum a2) => t -> [([a1], [a2])]
c 7 = [([a8,a7],[8,x7]) | x7 <- [3..7], a8 <- (pSet 8), a7 <- (filter (isCyclic a8) (pSet x7))]
c i = [(fst ci ++ [ai], snd ci ++ [xi]) | ci <- (c (i+1)), xi <- ([3..7] \\ (snd ci)), ai <- (filter (isCyclic ((last.fst) ci)) (pSet xi))]

fin = [k | k <- (c 3), isCyclic ((last.fst) k) ((head.fst) k)]