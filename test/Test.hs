module Test where

import Regularity

data Nat
  = Z
  | S Nat

{-# ANN add Regular #-}
add :: Nat -> Nat -> Nat
add Z y = y
add (S x) y = S (add x y)