{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Complex
  ( Cplx (CReal, CImag, CCart),
    i,
    conj,
    cre,
    cim,
  )
where

import Data.Kind (Type)
import Data.Ratio (denominator)
import GHC.Real (numerator)

data Cplx :: Type -> Type where
  CZero :: Cplx a
  CReal :: a -> Cplx a
  CImag :: a -> Cplx a
  CCart :: a -> a -> Cplx a

i :: Num a => Cplx a
i = CImag 1

cre, cim :: Num a => Cplx a -> a
cre CZero = 0
cre (CImag _) = 0
cre (CReal x) = x
cre (CCart x _) = x
cim CZero = 0
cim (CReal _) = 0
cim (CImag x) = x
cim (CCart _ x) = x

instance (Num a, Eq a) => Eq (Cplx a) where
  z1 == z2 = cre z1 == cre z2 && cim z1 == cim z2

norm :: (Num a, Eq a) => Cplx a -> Cplx a
norm CZero = CZero
norm (CReal 0) = CZero
norm (CImag 0) = CZero
norm (CCart 0 0) = CZero
norm (CReal x) = CReal x
norm (CCart x 0) = CReal x
norm (CImag y) = CImag y
norm (CCart 0 y) = CImag y
norm z = z

conj :: Num a => Cplx a -> Cplx a
conj CZero = CZero
conj (CReal x) = CReal x
conj (CImag y) = CImag (-y)
conj (CCart x y) = CCart x (-y)

instance (Floating a, Eq a) => Num (Cplx a) where
  CZero + z = z
  z + CZero = z
  (CReal x) + (CReal a) = norm $ CReal (x + a)
  (CReal x) + (CImag b) = CCart x b
  (CReal x) + (CCart a b) = norm $ CCart (x + a) b
  (CImag y) + (CReal a) = CCart a y
  (CImag y) + (CImag b) = norm $ CImag (y + b)
  (CImag y) + (CCart a b) = norm $ CCart a (y + b)
  (CCart x y) + (CReal a) = norm $ CCart (x + a) y
  (CCart x y) + (CImag b) = norm $ CCart x (y + b)
  (CCart x y) + (CCart a b) = norm $ CCart (x + a) (y + b)
  CZero * _ = CZero
  _ * CZero = CZero
  (CReal x) * (CReal a) = CReal (x * a)
  (CReal x) * (CImag b) = CImag (x * b)
  (CReal x) * (CCart a b) = CCart (x * a) (x * b)
  (CImag y) * (CReal a) = CImag (y * a)
  (CImag y) * (CImag b) = CReal (-1 * y * b)
  (CImag y) * (CCart a b) = CCart (-1 * y * b) (y * a)
  (CCart x y) * (CReal a) = CCart (x * a) (y * a)
  (CCart x y) * (CImag b) = CCart (-1 * y * b) (x * b)
  (CCart x y) * (CCart a b) = norm $ CCart (x * a - y * b) (x * b + y * a)
  abs = norm . CReal . abs'
  signum x = x / abs x
  fromInteger = norm . CReal . fromInteger
  negate CZero = CZero
  negate (CReal x) = CReal (-x)
  negate (CImag x) = CImag (-x)
  negate (CCart x y) = CCart (-x) (-y)

instance (Floating a, Eq a) => Fractional (Cplx a) where
  fromRational = norm . (((/) . CReal . fromInteger . numerator) <*> (CReal . fromInteger . denominator))
  recip z = conj z / square (abs z)

instance (Floating a, Ord a) => Floating (Cplx a) where
  pi = CReal pi
  exp CZero = 1
  exp (CReal x) = CReal (exp x) -- e^x = e^x
  exp (CImag theta) = CCart (cos theta) (sin theta) -- e^iθ = cos θ + i sin θ
  exp (CCart x theta) = CReal (exp x) * exp (CImag theta)
  sin x = -i * sinh (x * i)
  cos x = cosh (x * i)
  asin x = -i * asinh (x * i)
  acos x = -i * acosh x
  sinh x = (exp x - exp (-x)) / 2
  cosh x = (exp x + exp (-x)) / 2
  asinh x = log (x + sqrt (square x + 1))
  acosh x = log (x + sqrt (square x - 1))
  atanh x = log ((1 + x) / (1 - x)) / 2
  atan x = -i * atanh (i * x)
  log CZero = undefined
  log (CReal x) = CReal (log x)
  log (CImag x) = CCart (log $ abs x) (if x < 0 then -pi / 2 else pi / 2)
  log z@(CCart x y) = CCart (log $ abs' z) (atan2' y x)

abs' :: Floating a => Cplx a -> a
abs' CZero = 0
abs' (CReal x) = x
abs' (CImag x) = x
abs' (CCart x y) = abs'' x y

abs'' :: Floating a => a -> a -> a
abs'' x y = sqrt ((x * x) + (y * y))

atan2' :: (Floating a, Ord a) => a -> a -> a
atan2' y x
  | x > 0 = 2 * atan (y / (x + abs'' x y))
  | x <= 0 && y /= 0 = 2 * atan ((abs'' x y - x) / y)
  | x < 0 && y == 0 = pi
  | otherwise = error "(0, 0) has no angle. (atan2 computation)"

square :: Num a => a -> a
square x = x * x

instance Show a => Show (Cplx a) where
  show CZero = "0"
  show (CReal a) = show a
  show (CImag b) = show b
  show (CCart a b) = show a ++ "+i(" ++ show b ++ ")"
