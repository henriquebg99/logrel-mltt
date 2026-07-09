import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.Nat2 where
open import Definition.Typed.EqualityRelation
open EqRelSet {{...}}
open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Tools.Product
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
