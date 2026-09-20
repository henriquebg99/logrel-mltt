-- Maybe type.

{-# OPTIONS --safe #-}

module Tools.Maybe where

open import Tools.PropositionalEquality

open import Agda.Builtin.Maybe using (Maybe; just; nothing) public

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl
