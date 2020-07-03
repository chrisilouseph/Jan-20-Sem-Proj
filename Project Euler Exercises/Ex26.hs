reciCycle :: (Integral a, Read a) => a -> Int
reciCycle n = [ x | x <- [1..], mod (read (replicate x '9')) n == 0 ]!!0

a = filter mod25 [7..999]
    where mod25 x = (odd x && mod x 5 > 0)
t = map reciCycle a