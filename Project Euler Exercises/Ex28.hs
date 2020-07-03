prodSpiral :: (Num p, Eq p) => p -> p
prodSpiral 1 = 1
prodSpiral size = 4 * size^2 - 6 * (size-1) + prodSpiral (size-2)