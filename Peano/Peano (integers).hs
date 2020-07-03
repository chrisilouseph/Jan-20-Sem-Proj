-- The data type implementing the integers with Zero, positive integers (P) and negative integers (N)
-- Eg. 2 will be implemented as (P (P Zero)), while -2 will be (N (P (P Zero)))
data Peano = Zero | P Peano | N Peano deriving (Eq, Show, Read)

-- The successor function s
s :: Peano -> Peano
s Zero = P Zero
s (N (P Zero)) = Zero
s (P a) = P (P a)
s (N (P b)) = N b

-- The inverse of s
s' :: Peano -> Peano
s' Zero = N (P Zero)
s' (P a) = a
s' (N (P b)) = N (P (P b))

-- Converting a Peano to Int
see :: Peano -> Int
see Zero = 0
see (N b) = - see b
see a = 1 + (see $ s' a)

-- Converting Int to Peano
see' :: Int -> Peano
see' x
    | x == 0 = Zero
    | x > 0 = P $ see' $ x-1
    | otherwise = N $ see' $ -x

-- Defining addition
add :: Peano -> Peano -> Peano
add x Zero = x
add x y@(P b) = add (s x) (s' y)
add x y@(N b) = add (s' x) (s y)

-- Defining subtraction
sub :: Peano -> Peano -> Peano
sub x Zero = x
sub x y@(P b) = add x (N y)
sub x y@(N b) = add x b

--Defining order
comp a b = case sub a b of
    Zero -> EQ
    N x -> LT
    P x -> GT

-- Defining multiplication
mult :: Peano -> Peano -> Peano
mult _ Zero = Zero
mult a (P b) = add a $ mult a b
mult a (N b) = N $ mult a b