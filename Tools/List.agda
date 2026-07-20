{-# OPTIONS --safe #-}

module Tools.List where

infixr 30 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs