{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Substitution.Introductions.Nat (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.Properties equiv
open import Definition.LogicalRelation.Substitution equiv
open import Definition.LogicalRelation.Substitution.Introductions.Universe equiv

open import Tools.Product


-- Validity of the natural number type.
ℕᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ] / [Γ]
ℕᵛ [Γ] ⊢Δ [σ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Δ))) , λ _ x₂ → id (univ (ℕⱼ ⊢Δ)) 

-- Validity of the natural number type as a term.
ℕᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ι ¹ ⟩ ℕ ∷ Univ ! ⁰  ^ [ ! , ι ¹ ] / [Γ] / Uᵛ emb< [Γ]
ℕᵗᵛ [Γ] ⊢Δ [σ] = let Uℕₜ = Uₜ ℕ (idRedTerm:*: (ℕⱼ ⊢Δ)) ℕₙ (≅ₜ-ℕrefl ⊢Δ) (λ x ⊢Δ₁ → ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Δ₁))))
                in  Uℕₜ , λ x ⊢Δ₁ → Uₜ₌ Uℕₜ Uℕₜ (≅ₜ-ℕrefl ⊢Δ) λ [ρ] ⊢Δ₂ → (id (univ (ℕⱼ ⊢Δ₂)))


-- Validity of zero.
zeroᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ zero ∷ ℕ ^ [ ! , ι ⁰ ] / [Γ] / ℕᵛ [Γ]
zeroᵛ [Γ] ⊢Δ [σ] =
  ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) (≅ₜ-zerorefl ⊢Δ) zeroᵣ
    , (λ _ x₁ → ℕₜ₌ zero zero (idRedTerm:*: (zeroⱼ ⊢Δ)) (idRedTerm:*: (zeroⱼ ⊢Δ))
                    (≅ₜ-zerorefl ⊢Δ) zeroᵣ)

-- Validity of successor of valid natural numbers.
sucᵛ : ∀ {Γ n l} ([Γ] : ⊩ᵛ Γ)
         ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ] / [Γ])
     → Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ ^ [ ! , ι ⁰ ] / [Γ] / [ℕ]
     → Γ ⊩ᵛ⟨ l ⟩ suc n ∷ ℕ ^ [ ! , ι ⁰ ] / [Γ] / [ℕ]
sucᵛ ⊢Γ [ℕ] [n] ⊢Δ [σ] =
  sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
  , (λ x x₁ → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))

-- Validity of the second natural number type.
ℕ2ᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ]
ℕ2ᵛ [Γ] ⊢Δ [σ] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ))) , λ _ x₂ → id (univ (ℕ2ⱼ ⊢Δ))

-- Validity of the second natural number type as a term.
ℕ2ᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ι ¹ ⟩ ℕ2 ∷ Univ ! ⁰  ^ [ ! , ι ¹ ] / [Γ] / Uᵛ emb< [Γ]
ℕ2ᵗᵛ [Γ] ⊢Δ [σ] = let Uℕ2ₜ = Uₜ ℕ2 (idRedTerm:*: (ℕ2ⱼ ⊢Δ)) ℕ2ₙ (≅ₜ-ℕ2refl ⊢Δ) (λ x ⊢Δ₁ → ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ₁))))
                in  Uℕ2ₜ , λ x ⊢Δ₁ → Uₜ₌ Uℕ2ₜ Uℕ2ₜ (≅ₜ-ℕ2refl ⊢Δ) λ [ρ] ⊢Δ₂ → (id (univ (ℕ2ⱼ ⊢Δ₂)))

-- Validity of zero2.
zero2ᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ zero2 ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] / ℕ2ᵛ [Γ]
zero2ᵛ [Γ] ⊢Δ [σ] =
  ℕ2ₜ zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) (≅ₜ-zero2refl ⊢Δ) zero2ᵣ
    , (λ _ x₁ → ℕ2ₜ₌ zero2 zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) (idRedTerm:*: (zero2ⱼ ⊢Δ))
                    (≅ₜ-zero2refl ⊢Δ) zero2ᵣ)

-- Validity of successor of valid second natural numbers.
suc2ᵛ : ∀ {Γ n l} ([Γ] : ⊩ᵛ Γ)
         ([ℕ2] : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
     → Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] / [ℕ2]
     → Γ ⊩ᵛ⟨ l ⟩ suc2 n ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] / [ℕ2]
suc2ᵛ ⊢Γ [ℕ2] [n] ⊢Δ [σ] =
  suc2Term (proj₁ ([ℕ2] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
  , (λ x x₁ → suc2EqTerm (proj₁ ([ℕ2] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))
