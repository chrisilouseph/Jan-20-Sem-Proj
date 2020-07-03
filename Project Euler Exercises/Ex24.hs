sub :: (Eq a) => [a] -> [a] -> [a]
sub a b = [ x | x <- a, not (elem x b) ]

a = [ [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9] | x0 <- [0..9], x1 <- (sub [0..9] [x0]), x2 <- (sub [0..9] [x0,x1]), x3 <- (sub [0..9] [x0,x1,x2]), x4 <- (sub [0..9] [x0,x1,x2,x3]), x5 <- (sub [0..9] [x0,x1,x2,x3,x4]), x6 <- (sub [0..9] [x0,x1,x2,x3,x4,x5]), x7 <- (sub [0..9] [x0,x1,x2,x3,x4,x5,x6]), x8 <- (sub [0..9] [x0,x1,x2,x3,x4,x5,x6,x7]), x9 <- (sub [0..9] [x0,x1,x2,x3,x4,x5,x6,x7,x8]) ]!!999999