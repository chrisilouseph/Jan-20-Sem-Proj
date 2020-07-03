import Data.List ((\\))

isSquare x = ((^2).floor.sqrt.fromIntegral) x == x

minSol d = head [(y,d) | y <- [1..], isSquare (1 + d*y^2)]

noSquare = filter (not.isSquare) [2..233]
check = noSquare \\ idk

idk = [61,97,106,109,139,149,151,157,163,166,181,193,199,211,214,233]