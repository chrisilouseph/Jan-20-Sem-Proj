-- The data type implementing the natural numbers with Zero and the succ function S
data Peano = Zero | S Peano deriving (Show, Read)

-- The inverse of S
s' :: Peano -> Peano
s' Zero = error "Zero has no predecessor"
s' (S a) = a

-- Converting a Peano to Int
see :: Peano -> Int
see Zero = 0
see (S a) = 1 + see a

-- Converting Int to Peano
see' :: Int -> Peano
see' 0 = Zero
see' x
    | x > 0 = S $ see' $ x-1
    | otherwise = error "Trying to convert negative int to Peano"

-- Defining order
comp :: Peano -> Peano -> Ordering
comp Zero Zero = EQ
comp _ Zero = GT
comp Zero _ = LT
comp (S a) (S b) = comp a b

-- Defining addition
add :: Peano -> Peano -> Peano
add x Zero = x
add a (S b) = add (S a) b

-- Defining subtraction
sub :: Peano -> Peano -> Peano
sub a Zero = a
sub Zero b = error "First argument of sub less than the second"
sub (S a) (S b) = sub a b

-- Defining multiplication
mult :: Peano -> Peano -> Peano
mult _ Zero = Zero
mult a (S b) = add a $ mult a b

-- Defining division
divi :: Peano -> Peano -> Peano
divi _ Zero = error "Division by Zero"
divi Zero _ = Zero
divi a b
    | comp a b == LT = error "Not divisible"
    | otherwise = S $ divi (sub a b) b