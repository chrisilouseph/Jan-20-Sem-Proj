pythTrip p = [ (a,b,p-a-b) | a <- [1..p-2], b <- [a..p-a-1], a^2 + b^2 == (p-a-b)^2 ]

t = [length (pythTrip p) | p <- [5..1000] ]