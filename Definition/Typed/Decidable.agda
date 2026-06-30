{-# OPTIONS --safe #-}

import Definition.Equiv as E
module Definition.Typed.Decidable (equiv : E.Equiv) where

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.Typed.Consequences.Syntactic equiv
open import Definition.Conversion equiv
open import Definition.Conversion.Decidable equiv
open import Definition.Conversion.Soundness equiv
open import Definition.Conversion.Stability equiv
open import Definition.Conversion.Consequences.Completeness equiv

open import Tools.Nullary
open import Tools.Product
open import Tools.Nat


-- Decidability of conversion of well-formed types
dec : ∀ {A B r Γ} → Γ ⊢ A ^ r → Γ ⊢ B ^ r → Dec (Γ ⊢ A ≡ B ^ r)
dec ⊢A ⊢B =
  let ⊢Γ≡Γ = reflConEq (wf ⊢A)
  in  map soundnessConv↑ completeEq
          (decConv↑ ⊢Γ≡Γ (completeEq (refl ⊢A)) (completeEq (refl ⊢B)) (le-suc (le-refl _) ))

-- Decidability of conversion of well-formed terms
decTerm : ∀ {t u A r Γ} → Γ ⊢ t ∷ A ^ r → Γ ⊢ u ∷ A ^ r → Dec (Γ ⊢ t ≡ u ∷ A ^ r)
decTerm {r = [ ! , l ]} ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map soundnessConv↑Term completeEqTerm
          (decConv↑TermConv ⊢Γ≡Γ (refl (syntacticTerm ⊢t)) (completeEqTerm (genRefl ⊢t)) (completeEqTerm (genRefl ⊢u)) (le-suc (le-refl _) ))
decTerm {r = [ % , l ]} ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map (λ x → proj₂ (proj₂ (soundness~↑% x))) completeEqTerm
          (decConv↑TermConv ⊢Γ≡Γ (refl (syntacticTerm ⊢t)) (completeEqTerm (genRefl ⊢t)) (completeEqTerm (genRefl ⊢u)) (le-suc (le-refl _) ))
