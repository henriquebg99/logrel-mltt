{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Substitution.Conversion (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.LogicalRelation.Irrelevance equiv
open import Definition.LogicalRelation.Properties equiv
open import Definition.LogicalRelation.Substitution equiv

open import Tools.Product


-- Conversion from left to right of valid terms.
convᵛ : ∀ {t A B r Γ l}
        ([Γ] : ⊩ᵛ Γ)
        ([A]  : Γ ⊩ᵛ⟨ l ⟩ A ^ r / [Γ])
        ([B]  : Γ ⊩ᵛ⟨ l ⟩ B ^ r / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ r / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ r / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ∷ B ^ r / [Γ] / [B]
convᵛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₁ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ′] [σ≡σ′] → convEqTerm₁ [σA] [σB] [σA≡σB] ([σt≡σ′t] [σ′] [σ≡σ′])

-- Conversion from right to left of valid terms.
conv₂ᵛ : ∀ {t A B r Γ l}
         ([Γ] : ⊩ᵛ Γ)
         ([A]  : Γ ⊩ᵛ⟨ l ⟩ A ^ r / [Γ])
         ([B]  : Γ ⊩ᵛ⟨ l ⟩ B ^ r / [Γ])
       → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ r / [Γ] / [A]
       → Γ ⊩ᵛ⟨ l ⟩ t ∷ B ^ r / [Γ] / [B]
       → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ r / [Γ] / [A]
conv₂ᵛ [Γ] [A] [B] [A≡B] [t] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
      [σt]     = proj₁ ([t] ⊢Δ [σ])
      [σt≡σ′t] = proj₂ ([t] ⊢Δ [σ])
  in  convTerm₂ [σA] [σB] [σA≡σB] [σt]
  ,   λ [σ′] [σ≡σ′] → convEqTerm₂ [σA] [σB] [σA≡σB] ([σt≡σ′t] [σ′] [σ≡σ′])

-- Conversion from left to right of valid term equality.
convEqᵛ : ∀ {t u A B r Γ l}
        ([Γ] : ⊩ᵛ Γ)
        ([A]  : Γ ⊩ᵛ⟨ l ⟩ A ^ r / [Γ])
        ([B]  : Γ ⊩ᵛ⟨ l ⟩ B ^ r / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ r / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ r / [Γ] / [A]
      → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B ^ r / [Γ] / [B]
convEqᵛ [Γ] [A] [B] [A≡B] [t≡u] ⊢Δ [σ] =
  let [σA]     = proj₁ ([A] ⊢Δ [σ])
      [σB]     = proj₁ ([B] ⊢Δ [σ])
      [σA≡σB]  = irrelevanceEq [σA] [σA] ([A≡B] ⊢Δ [σ])
  in  convEqTerm₁ [σA] [σB] [σA≡σB] ([t≡u] ⊢Δ [σ])
