{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Dual (dconj, norm, Dual (..), epsilon) where

import Data.Kind (Type)

square :: Num a => a -> a
square x = x * x

data Dual :: Type -> Type where
  DZero :: Dual a
  DReal :: a -> Dual a
  DEps :: a -> Dual a
  DCart :: a -> a -> Dual a

dre, dim :: Num a => Dual a -> a
dre DZero = 0
dre (DEps _) = 0
dre (DReal x) = x
dre (DCart x _) = x
dim DZero = 0
dim (DReal _) = 0
dim (DEps x) = x
dim (DCart _ x) = x

instance (Eq a, Num a) => Eq (Dual a) where
  z1 == z2 = dre z1 == dre z2 && dim z1 == dim z2

dconj :: Num a => Dual a -> Dual a
dconj DZero = DZero
dconj (DReal x) = DReal x
dconj (DEps x) = DEps (-x)
dconj (DCart x y) = DCart x (-y)

norm :: (Eq a, Num a) => Dual a -> Dual a
norm DZero = DZero
norm (DReal 0) = DZero
norm (DEps 0) = DZero
norm (DCart 0 0) = DZero
norm (DReal x) = DReal x
norm (DEps e) = DEps e
norm (DCart 0 e) = DEps e
norm (DCart x 0) = DReal x
norm (DCart x e) = DCart x e

epsilon :: Num a => Dual a
epsilon = DEps 1

instance (Fractional a, Eq a) => Num (Dual a) where
  DZero + z = z
  z + DZero = z
  (DReal x) + (DReal a) = norm $ DReal (x + a)
  (DReal x) + (DEps b) = DCart x b
  (DReal x) + (DCart a b) = norm $ DCart (x + a) b
  (DEps y) + (DReal a) = DCart a y
  (DEps y) + (DEps b) = norm $ DEps (y + b)
  (DEps y) + (DCart a b) = norm $ DCart a (y + b)
  (DCart x y) + (DReal a) = norm $ DCart (x + a) y
  (DCart x y) + (DEps b) = norm $ DCart x (y + b)
  (DCart x y) + (DCart a b) = norm $ DCart (x + a) (y + b)
  _ * DZero = DZero
  DZero * _ = DZero
  (DReal x) * (DReal a) = DReal (x * a)
  (DReal x) * (DEps b) = DEps (x * b)
  (DReal x) * (DCart a b) = DCart (x * a) (x * b)
  (DEps y) * (DReal a) = DEps (y * a)
  (DEps _) * (DEps _) = DReal 0
  (DEps y) * (DCart _ b) = DEps (y * b)
  (DCart x y) * (DReal a) = DCart (x * a) (y * a)
  (DCart x _) * (DEps b) = DEps (x * b)
  (DCart x y) * (DCart a b) = norm $ DCart (x * a) (x * b + y * a)

  abs DZero = DZero
  abs (DReal x) = DReal $ abs x
  abs (DEps _) = DReal 0
  abs (DCart x _) = DReal $ abs x
  signum DZero = DZero
  signum (DReal x) = DReal (signum x)
  signum (DEps _) = undefined
  signum (DCart x e) = DCart (signum x) (e / abs x)
  fromInteger = DReal . fromInteger
  negate DZero = DZero
  negate (DReal x) = DReal (-x)
  negate (DEps e) = DEps (-e)
  negate (DCart x e) = DCart (-x) (-e)

instance (Fractional a, Eq a) => Fractional (Dual a) where
  fromRational = DReal . fromRational
  recip DZero = undefined
  recip (DReal x) = DReal (recip x)
  recip (DEps _) = error "reciprocal of non-real dual number is undefined"
  recip (DCart x e) = DCart (recip x) (-e / square x)

instance (Floating a, Eq a) => Floating (Dual a) where
  pi = DReal pi
  exp DZero = 1
  exp (DReal x) = DReal (exp x)
  exp (DEps e) = DCart 1 e
  exp (DCart x e) = DCart (exp x) (e * exp x)
  log DZero = undefined
  log (DReal x) = DReal (log x)
  log (DEps _) = error "log of non-real dual number is undefined"
  log (DCart x e) = DCart (log x) (e / x)
  sin DZero = DZero
  sin (DReal x) = DReal (sin x)
  sin (DEps e) = DReal e
  sin (DCart x e) = DCart (sin x) (e * cos x)
  cos DZero = 1
  cos (DReal x) = DReal (cos x)
  cos (DEps _) = DReal 0
  cos (DCart x e) = DCart (cos x) (-e * sin x)
  asin DZero = DZero
  asin (DReal x) = DReal (asin x)
  asin (DEps e) = DEps e
  asin (DCart x e) = DCart (asin x) (e / sqrt (1 - square x))
  acos DZero = pi / 2
  acos (DReal x) = DReal (acos x)
  acos (DEps e) = DEps (-e)
  acos (DCart x e) = DCart (acos x) (-e / sqrt (1 - square x))
  atan DZero = DZero
  atan (DReal x) = DReal (atan x)
  atan (DEps e) = DEps e
  atan (DCart x e) = DCart (atan x) (e / (1 + square x))
  asinh DZero = DZero
  asinh (DReal x) = DReal (asinh x)
  asinh (DEps e) = DEps e
  asinh (DCart x e) = DCart (asinh x) (e / sqrt (1 + square x))
  acosh DZero = undefined
  acosh (DReal x) = DReal (acosh x)
  acosh (DEps _) = error "arcosh's derivative is non-real at zero."
  acosh (DCart x e) = DCart (acosh x) (e / sqrt (square x - 1))
  sinh DZero = DZero
  sinh (DReal x) = DReal (sinh x)
  sinh (DEps e) = DEps e
  sinh (DCart x e) = DCart (sinh x) (e * cosh x)
  cosh DZero = 1
  cosh (DReal x) = DReal (cosh x)
  cosh (DEps _) = DEps 0
  cosh (DCart x e) = DCart (cosh x) (e * sinh x)
  atanh DZero = DZero
  atanh (DReal x) = DReal (atanh x)
  atanh (DEps e) = DEps e
  atanh (DCart x e) = DCart (atanh x) (e / (1 - square x))

instance Show a => Show (Dual a) where
  show DZero = "0"
  show (DReal x) = show x
  show (DEps e) = show e ++ "ϵ"
  show (DCart x e) = show x ++ "+" ++ show e ++ "ϵ"
