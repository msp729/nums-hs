{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Double () where

import Data.Kind (Type)

data Dbl :: Type -> Type where
  DbZ :: Dbl a
  DbR :: a -> Dbl a
  DbE :: a -> Dbl a
  DbC :: a -> a -> Dbl a

dbr, dbe :: Num a => Dbl a -> a
dbr DbZ = 0
dbr (DbE _) = 0
dbr (DbR x) = x
dbr (DbC x _) = x
dbe DbZ = 0
dbe (DbR _) = 0
dbe (DbE x) = x
dbe (DbC _ x) = x

norm :: (Num a, Eq a) => a -> a -> Dbl a
norm 0 0 = DbZ
norm 0 e = DbE e
norm x 0 = DbR x
norm x e = DbC x e

instance (Num a, Eq a, Floating a) => Num (Dbl a) where
  DbZ + d = d
  d + DbZ = d
  DbR x + DbR a = norm (x + a) 0
  DbR x + DbE b = DbC x b
  DbR x + DbC a b = norm (x + a) b
  DbE y + DbR a = DbC a y
  DbE y + DbE b = norm 0 (b + y)
  DbE y + DbC a b = norm a (y + b)
  DbC x y + DbR a = norm (x + a) y
  DbC x y + DbE b = norm x (y + b)
  DbC x y + DbC a b = norm (x + a) (y + b)
  DbZ * _ = DbZ
  _ * DbZ = DbZ
  z1 * z2 = norm (dbr z1 * dbr z2 + dbe z1 * dbe z2) (dbr z1 * dbe z2 + dbe z1 * dbr z2)
  negate DbZ = DbZ
  negate (DbR x) = DbR (-x)
  negate (DbE x) = DbE (-x)
  negate (DbC x e) = DbC (-x) (-e)
  abs DbZ = DbZ
  abs (DbR x) = DbR $ abs x
  abs (DbE y) = DbR $ sqrt (-y * y)
  abs (DbC x y) = DbR $ sqrt (x * x - y * y)
  signum = _
  fromInteger = DbR . fromInteger
