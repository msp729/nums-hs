module Main (main) where

import Complex ()
import Dual (Dual (DCart))

z, z' :: Dual Double
z = DCart 3 2
z' = sinh z

main :: IO ()
main = do
  print z
  print z'
