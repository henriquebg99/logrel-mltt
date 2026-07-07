{-# OPTIONS --safe #-}

import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
import Definition.LogicalRelation.EquivRed as ERd
module Definition.Typed.Consequences.Decidable
  (equiv : E.Equiv)
  (equivRed : forall (eqrel : ER.EqRelSet equiv) → ERd.EquivRed equiv eqrel) where

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.Typed.EqRelInstance equiv
open import Definition.Conversion equiv
open import Definition.Conversion.Stability equiv equivRed
open import Definition.Conversion.Soundness equiv equivRed
open import Definition.Conversion.Decidable equiv equivRed
open import Definition.Conversion.Consequences.Completeness equiv equivRed

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

-- Decidability of algorithmic equality of neutrals.
dec-aux : ∀ {Γ t u T l}
        → Dec (Γ ⊢ t [conv↑] u ∷ T ^ l)
        → Dec (Γ ⊢ t ≡ u ∷ T ^ [ ! , l ])
dec-aux (yes p) = yes (soundnessConv↑Term p)
dec-aux (no ¬p) = no λ x → ¬p (completeEqTerm x)


dec : ∀ {Γ t u T l}
        → (⊢t : Γ ⊢ t ∷ T ^ [ ! , l ])
        → (⊢u : Γ ⊢ u ∷ T ^ [ ! , l ])
        → Dec (Γ ⊢ t ≡ u ∷ T ^ [ ! , l ])
dec ⊢t ⊢u = dec-aux (decConv↑Term (reflConEq (wfTerm ⊢t)) (completeEqTerm (refl ⊢t)) (completeEqTerm (refl ⊢u)) (le-refl _))
