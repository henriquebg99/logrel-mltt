{-# OPTIONS --safe #-}

import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.EquivRed (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped hiding (wk)
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.Typed.RedSteps equiv
import Definition.Typed.Weakening equiv as Twk
open Twk using (_∷_⊆_)
open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.Properties equiv
open import Definition.LogicalRelation.Irrelevance equiv
import Definition.LogicalRelation.Weakening equiv as Lwk

open import Tools.Product
open import Tools.Empty using (⊥-elim)
import Tools.PropositionalEquality as PE

Πℕℕ2 : ∀ {Γ} → (⊢Γ : ⊢ Γ) →
  Γ ⊩⟨ ι ⁰ ⟩ Π ℕ ^ ! ° ⁰ ▹ ℕ2 ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
Πℕℕ2 {Γ} ⊢Γ =
  let Dℕ = idRed:*: (univ (ℕⱼ ⊢Γ))
      [ℕ] = ℕᵣ Dℕ
      ⊢ℕ = univ (ℕⱼ ⊢Γ)
      ⊢Γℕ = _∙_ ⊢Γ ⊢ℕ
      ⊢G = univ (ℕ2ⱼ ⊢Γℕ)
      ⊢Π = Πⱼ (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ (ℕⱼ ⊢Γ) ▹ (ℕ2ⱼ ⊢Γℕ)
      [G] : ∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
          → Δ ⊩⟨ ι ⁰ ⟩ ℕ2 ^ [ ! , ι ⁰ ]
      [G] [ρ] ⊢Δ [a] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))
      G-ext : ∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
            → ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
            → ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
            → Δ ⊩⟨ ι ⁰ ⟩ ℕ2 ≡ ℕ2 ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [a]
      G-ext [ρ] ⊢Δ [a] [b] [a≡b] = reflEq ([G] [ρ] ⊢Δ [a])
  in Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) ℕ ℕ2 (idRed:*: (univ ⊢Π)) ⊢ℕ ⊢G
       (≅-univ (≅ₜ-Π-cong (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) (λ abs → ⊥-elim (!≢% abs)) ⊢ℕ
                 (≅ₜ-ℕrefl ⊢Γ) (≅ₜ-ℕ2refl ⊢Γℕ)))
       (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ [ℕ])
       [G] G-ext

Πℕ2ℕ : ∀ {Γ} → (⊢Γ : ⊢ Γ) →
  Γ ⊩⟨ ι ⁰ ⟩ Π ℕ2 ^ ! ° ⁰ ▹ ℕ ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
Πℕ2ℕ {Γ} ⊢Γ =
  let Dℕ2 = idRed:*: (univ (ℕ2ⱼ ⊢Γ))
      [ℕ2] = ℕ2ᵣ Dℕ2
      ⊢ℕ2 = univ (ℕ2ⱼ ⊢Γ)
      ⊢Γℕ2 = _∙_ ⊢Γ ⊢ℕ2
      ⊢G = univ (ℕⱼ ⊢Γℕ2)
      ⊢Π = Πⱼ (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ (ℕ2ⱼ ⊢Γ) ▹ (ℕⱼ ⊢Γℕ2)
      [G] : ∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ ℕ2 ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ2])
          → Δ ⊩⟨ ι ⁰ ⟩ ℕ ^ [ ! , ι ⁰ ]
      [G] [ρ] ⊢Δ [a] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Δ)))
      G-ext : ∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ ℕ2 ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ2])
            → ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ ℕ2 ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ2])
            → ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ ℕ2 ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ2])
            → Δ ⊩⟨ ι ⁰ ⟩ ℕ ≡ ℕ ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [a]
      G-ext [ρ] ⊢Δ [a] [b] [a≡b] = reflEq ([G] [ρ] ⊢Δ [a])
  in Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) ℕ2 ℕ (idRed:*: (univ ⊢Π)) ⊢ℕ2 ⊢G
       (≅-univ (≅ₜ-Π-cong (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) (λ abs → ⊥-elim (!≢% abs)) ⊢ℕ2
                 (≅ₜ-ℕ2refl ⊢Γ) (≅ₜ-ℕrefl ⊢Γℕ2)))
       (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ [ℕ2])
       [G] G-ext

record EquivRed : Set₁ where
  field
    [fwd] : ∀ {Γ} (⊢Γ : ⊢ Γ)
          → let [Π] = Πℕℕ2 ⊢Γ
            in Γ ⊩⟨ ι ⁰ ⟩ emb_oterm_term (E.Equiv.fwd equiv)
                 ∷ Π ℕ ^ ! ° ⁰ ▹ ℕ2 ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / [Π]
    [bwd] : ∀ {Γ} (⊢Γ : ⊢ Γ)
          → let [Π] = Πℕ2ℕ ⊢Γ
            in Γ ⊩⟨ ι ⁰ ⟩ emb_oterm_term (E.Equiv.bwd equiv)
                 ∷ Π ℕ2 ^ ! ° ⁰ ▹ ℕ ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / [Π]
