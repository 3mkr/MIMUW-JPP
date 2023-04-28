module SparsePoly(fromDP, toDP, qrP) where
import PolyClass
import Representation

-- | fromDP example
-- >>> fromDP sampleDP
-- S {unS = [(3,1),(0,-1)]}
fromDP :: (Eq a, Num a) => DensePoly a -> SparsePoly a
fromDP (P x) = canonFormSP (S (fromDPHelp x 0))

fromDPHelp :: (Eq a, Num a) => [a] -> Int -> [(Int, a)]
fromDPHelp [] n = []
fromDPHelp (x : xs) n = (n, x) : fromDPHelp xs (n + 1) 

toDP :: (Eq a, Num a) => SparsePoly a -> DensePoly a
toDP (S x) = canonFormDP (P (toDPHelp x (degree (S x)) [])) 

toDPHelp :: (Eq a, Num a) => [(Int, a)] -> Int -> [a] -> [a]
toDPHelp _ (-1) r = r
toDPHelp [] n r = toDPHelp [] (n - 1) (0 : r)
toDPHelp (x : xs) n r = if (fst x) == n
    then toDPHelp xs (n - 1) ((snd x) : r)
    else toDPHelp (x : xs) (n - 1) (0 : r)

canonFormDP :: (Eq a, Num a) => DensePoly a -> DensePoly a
canonFormDP (P xs) = P (reverse (canonFormHelpDP (reverse xs)))

canonFormHelpDP :: (Eq a, Num a) => [a] -> [a]
canonFormHelpDP [] = []
canonFormHelpDP (x : xs) = if x == 0 then canonFormHelpDP xs else (x : xs) 

first :: (a -> a') -> (a, b) -> (a', b)
first = undefined

instance Functor SparsePoly where
    fmap f (S x) = S (map (second f) x)

second :: (b -> b') -> (a, b) -> (a, b')
second f a = ((fst a), f (snd a))

instance Polynomial SparsePoly where
    zeroP           = S []
    constP c        = canonFormSP (S [(0, c)])
    varP            = S [(1, 1)]
    evalP (S a) x   = evalPHelpSP a x 0
    shiftP n (S a)  = canonFormSP (S (shiftHelpSP n a []))
    degree (S a)    = degreeHelp (canonFormSP (S a))

degreeHelp :: (Eq a, Num a) => SparsePoly a -> Int
degreeHelp (S []) = -1
degreeHelp (S (a : as)) = fst a

sortPoly :: [(Int, a)] -> [(Int, a)]
sortPoly [] = []
sortPoly (x : xs) = (sortPoly lesser) ++ [x] ++ (sortPoly greater)
    where
        lesser = filter (\(a, _) -> a < fst x) xs
        greater = filter (\(a, _) -> a > fst x) xs

reverseSortPoly :: [(Int, a)] -> [(Int, a)]
reverseSortPoly [] = []
reverseSortPoly (x : xs) = (reverseSortPoly greater) ++ [x] ++ (reverseSortPoly lesser)
    where
        lesser = filter (\(a, _) -> a < fst x) xs
        greater = filter (\(a, _) -> a > fst x) xs

canonFormSP :: (Eq a, Num a) => SparsePoly a -> SparsePoly a
canonFormSP (S xs) =  S (canonFormHelpSP (sortPoly xs) [])

canonFormHelpSP :: (Eq a, Num a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)]
canonFormHelpSP [] canon = canon
canonFormHelpSP (x : xs) canon = if (snd x) /= 0 then (canonFormHelpSP xs (x : canon)) else (canonFormHelpSP xs canon)

evalPHelpSP :: Num a => [(Int, a)] -> a -> a -> a
evalPHelpSP [] _ result = result
evalPHelpSP (a : as) x result = evalPHelpSP as x (result + ((snd a) * (powerSP x (fst a))))

powerSP :: Num a => a -> Int -> a
powerSP base 0 = 1
powerSP base 1 = base
powerSP base exp = base * powerSP base (exp - 1)

shiftHelpSP :: (Eq a, Num a) => Int -> [(Int, a)] -> [(Int, a)] -> [(Int, a)]
shiftHelpSP n [] shifted = shifted
shiftHelpSP n (a : as) shifted = shiftHelpSP n as ((addFst a n) : shifted)

addFst :: (Int, a) -> Int -> (Int, a)
addFst (a, b) n = (a + n, b)

instance (Eq a, Num a) => Num (SparsePoly a) where
    (+)         (S a) (S b) = canonFormSP (S (operationArraySP (\x y -> x) (+) (canonFormHelpSP (sortPoly a) []) (canonFormHelpSP (sortPoly b) [])))
    (-)         (S a) (S b) = canonFormSP (S (operationArraySP (\x y -> x) (-) (canonFormHelpSP (sortPoly a) []) (canonFormHelpSP (sortPoly b) [])))
    (*)         (S a) (S b) = canonFormSP (S (multiplyArraySP a b))
    negate      (S a)       = canonFormSP (S (map (\(x, y) -> (x, y * (-1))) a))
    fromInteger 0           = zeroP
    fromInteger x           = S [(0, fromIntegral x)]
    abs = undefined
    signum = undefined

operationArraySP :: Num a => (Int -> Int -> Int) -> (a -> a -> a) -> [(Int, a)] -> [(Int, a)] -> [(Int, a)] 
operationArraySP f g x y = operationArrayAccSP f g (reverseSortPoly (x)) (reverseSortPoly (y)) []

operationArrayAccSP :: Num a => (Int -> Int -> Int) -> (a -> a -> a) -> [(Int, a)] ->[(Int, a)] -> [(Int, a)] -> [(Int, a)]
operationArrayAccSP f g (x : xs) (y : ys) r =
    if (fst x) > (fst y)
        then operationArrayAccSP f g xs (y : ys) (x : r)
    else if (fst x) < (fst y)
       then operationArrayAccSP f g (x : xs) ys ((fst y, g 0 (snd y)) : r)
    else operationArrayAccSP f g xs ys ((tupleOperation f g x y) : r)

operationArrayAccSP f g (x : xs) [] r = operationArrayAccSP f g xs [] (x : r)
operationArrayAccSP f g [] (y : ys) r = operationArrayAccSP f g [] ys ((fst y, g 0 (snd y)) : r)
operationArrayAccSP f g [] [] r = r

tupleOperation :: Num a => (Int -> Int -> Int) -> (a -> a -> a) -> (Int, a) -> (Int, a) -> (Int, a)
tupleOperation f g a b = ((f (fst a)  (fst b)), (g (snd a) (snd b)))

multiplyArraySP :: Num a => [(Int, a)] -> [(Int, a)] -> [(Int, a)]
multiplyArraySP [] _ = []
multiplyArraySP (x : xs) ys = operationArraySP (\x y -> x) (+) (mul x ys) (multiplyArraySP xs ys)

mul :: Num a => (Int, a) -> [(Int, a)] -> [(Int, a)]
mul x [] = []
mul x (y : ys) = ((fst x) + (fst y), (snd x) * (snd y)) : (mul x ys)

instance (Eq a, Num a) => Eq (SparsePoly a) where
    p == q = nullP(p-q)

-- qrP s t | not(nullP t) = (q, r) iff s == q*t + r && degree r < degree t
qrP :: (Eq a, Fractional a) => SparsePoly a -> SparsePoly a -> (SparsePoly a, SparsePoly a)
qrP (S a) (S (b : bs)) = qrHelp a (b : bs) [] a (fst b) (snd b)

qrHelp :: (Eq a, Fractional a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)] -> [(Int, a)] -> Int -> a -> (SparsePoly a, SparsePoly a)
qrHelp _ _ q [] _ _ = (canonFormSP (S q), canonFormSP (S []))
qrHelp a b q (r : rs) d c = if (degHelp (r : rs) (-1)) >= d
    then let s = (((degHelp (r : rs) (-1)) - d), ((snd r) / c)) in qrHelp a b (operationArraySP (\x y -> x) (+) q [s]) ( canonFormHelpSP (operationArraySP (\x y -> x) (-) (r : rs) (mul s b)) []) d c
    else (canonFormSP (S q), canonFormSP (S (r : rs)))

degHelp :: (Eq a, Num a) => [(Int, a)] -> Int -> Int
degHelp [] max = max
degHelp (x : xs) max = if (fst x) > max && (snd x) /= 0 then degHelp xs (fst x) else degHelp xs max

-- | Division example
-- >>> qrP (x^2 - 1) (x -1) == ((x + 1), 0)
-- True
