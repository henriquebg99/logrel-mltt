{-# OPTIONS --safe #-}

import Definition.Equiv as E
module Definition.Conversion.Universe (equiv : E.Equiv) where

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.Typed.RedSteps equiv
open import Definition.Conversion equiv
open import Definition.Conversion.Reduction equiv
open import Definition.Conversion.Lift equiv

import Tools.PropositionalEquality as PE


-- Algorithmic equality of terms in WHNF of type U are equal as types.
univConv↓ : ∀ {A B r Γ l}
          → Γ ⊢ A [conv↓] B ∷ Univ r l ^ next l
          → Γ ⊢ A [conv↓] B ^ [ r , ι l ]
univConv↓ X = univ X

-- Algorithmic equality of terms of type U are equal as types.
univConv↑ : ∀ {A B r Γ l}
      → Γ ⊢ A [conv↑] B ∷ Univ r l ^ next l
      → Γ ⊢ A [conv↑] B ^ [ r , ι l ]
univConv↑ ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
      rewrite PE.sym (whnfRed* D Uₙ) =
  reductionConv↑ (univ* d) (univ* d′) whnft′ whnfu′ (liftConv (univConv↓ t<>u))
