module DensePoly() where
import PolyClass
import Representation

instance Functor DensePoly where
    fmap f (P x) = P (map f x)

instance Polynomial DensePoly where
    zeroP           = P []
    constP c        = canonFormDP (P [c])
    varP            = P [0, 1]
    evalP (P a) x   = evalPHelpDP a x 0 0
    shiftP n (P a)  = canonFormDP (P (shiftHelpDP n a))
    degree (P a)    = degreeHelp (canonFormDP (P a))

degreeHelp :: DensePoly a -> Int
degreeHelp (P a) = length a - 1

evalPHelpDP :: Num a => [a] -> a -> a -> Int -> a
evalPHelpDP [] _ result exp = result
evalPHelpDP (a : as) x result exp = evalPHelpDP as x (result + (a * (powerDP x exp))) (exp + 1)

shiftHelpDP :: (Eq a, Num a) => Int -> [a] -> [a]
shiftHelpDP 0 a = a
shiftHelpDP n a = if n < 0 then a else shiftHelpDP (n - 1) (0 : a)

powerDP :: Num a => a -> Int -> a
powerDP base 0 = 1
powerDP base 1 = base
powerDP base exp = base * powerDP base (exp - 1)

-- |
-- >>> x^3 - 1 :: DensePoly Integer 
-- P {unP = [-1,0,0,1]}

-- | Num operations give canonical results:
-- >>> isCanonicalDP (sampleDP - sampleDP)
-- True
    
instance (Eq a, Num a) => Eq (DensePoly a) where
    p == q = nullP(p-q)
    (/=) (P a) (P b) = a /= b

instance (Eq a, Num a) => Num (DensePoly a) where
    (+)         (P a) (P b) = canonFormDP (P (operationArrayDP (+) a b))
    (-)         (P a) (P b) = canonFormDP (P (operationArrayDP (-) a b))
    (*)         (P a) (P b) = canonFormDP (P (multiplyArrayDP a b))
    negate      (P a)       = canonFormDP (P (map (\x -> x * (-1)) a))
    fromInteger 0           = zeroP
    fromInteger x           = P [fromIntegral x]
    abs = undefined
    signum = undefined

operationArrayDP :: Num a => (a -> a -> a) -> [a] -> [a] -> [a]
operationArrayDP f x y = reverse (operationArrayAccDP  f x y [])

operationArrayAccDP :: Num a => (a -> a -> a) -> [a] -> [a] -> [a] -> [a]
operationArrayAccDP f [] [] r = r
operationArrayAccDP f [] (y : ys) r = operationArrayAccDP f [] ys ((f 0 y) : r)
operationArrayAccDP f (x : xs) [] r = operationArrayAccDP f xs [] (x : r)
operationArrayAccDP f (x : xs) (y : ys) r = operationArrayAccDP f xs ys ((f x y) : r)

multiplyArrayDP :: Num a => [a] -> [a] -> [a]
multiplyArrayDP [] _ = [0]
multiplyArrayDP (x : xs) ys = operationArrayDP (+) (map (*x) ys) (0 : (multiplyArrayDP (xs) ys))

canonFormDP :: (Eq a, Num a) => DensePoly a -> DensePoly a
canonFormDP (P xs) = P (reverse (canonFormHelpDP (reverse xs)))

canonFormHelpDP :: (Eq a, Num a) => [a] -> [a]
canonFormHelpDP [] = []
canonFormHelpDP (x : xs) = if x == 0 then canonFormHelpDP xs else (x : xs)

-- |
-- >>>  P [1,2] == P [1,2]
-- True

-- |
-- >>> fromInteger 0 == (zeroP :: DensePoly Int)
-- True

-- |
-- >>>  P [0,1] == P [1,0]
-- False

-- | Degree examples
-- >>> degree (zeroP :: DensePoly Int)
-- -1
-- >>> degree (constP 1 :: DensePoly Int)
-- 0