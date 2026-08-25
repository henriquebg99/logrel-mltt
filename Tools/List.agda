{-# OPTIONS --safe #-}

module Tools.List where

open import Tools.Nat

infixr 30 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_∷ʳ_ : {A : Set} → List A → A → List A
[]        ∷ʳ y = y ∷ []
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

-- [0, 1, …, n − 1]
range : Nat → List Nat
range 0 = []
range (1+ n) = range n ∷ʳ n
