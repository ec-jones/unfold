module Test where

import Regularity

data Nat
  = Z
  | S Nat

data List a
  = Nil
  | Cons a (List a)

{-# ANN add Regular #-}
add :: Nat -> Nat -> Nat
add Z y = y
add (S x) y = S (add x y)

{-# ANN append Regular #-}
append :: List Nat -> List Nat -> List Nat
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys) 