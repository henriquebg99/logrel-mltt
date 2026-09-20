-- We define a record with witnesses that the forward and backward
-- equivalences are reducible in the logical relation, for an instance of the 
-- generic equality

import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.EquivRed (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
import Definition.Equiv senv as Eq
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}

open import Definition.Untyped senv hiding (wk)
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.RedSteps senv equivs
import Definition.Typed.Weakening senv equivs as Twk
open Twk using (_∷_⊆_)
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.Properties senv equivs
open import Definition.LogicalRelation.Irrelevance senv equivs
import Definition.LogicalRelation.Weakening senv equivs as Lwk

open import Tools.Product
open import Tools.List using (_∈ₗ_)
open import Tools.Empty using (⊥-elim)
import Tools.PropositionalEquality as PE

Πℕℕ : ∀ {Γ} → (⊢Γ : ⊢ Γ) →
  Γ ⊩⟨ ι ⁰ ⟩ Π ℕ ^ ! ° ⁰ ▹ ℕ ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
Πℕℕ {Γ} ⊢Γ =
  let Dℕ = idRed:*: (univ (ℕⱼ ⊢Γ))
      [ℕ] = ℕᵣ Dℕ
      ⊢ℕ = univ (ℕⱼ ⊢Γ)
      ⊢Γℕ = _∙_ ⊢Γ ⊢ℕ
      ⊢G = univ (ℕⱼ ⊢Γℕ)
      ⊢Π = Πⱼ (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ (ℕⱼ ⊢Γ) ▹ (ℕⱼ ⊢Γℕ)
      [G] : ∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
          → Δ ⊩⟨ ι ⁰ ⟩ ℕ ^ [ ! , ι ⁰ ]
      [G] [ρ] ⊢Δ [a] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Δ)))
      G-ext : ∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
            → ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
            → ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ ℕ ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [ℕ])
            → Δ ⊩⟨ ι ⁰ ⟩ ℕ ≡ ℕ ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [a]
      G-ext [ρ] ⊢Δ [a] [b] [a≡b] = reflEq ([G] [ρ] ⊢Δ [a])
  in Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) ℕ ℕ (idRed:*: (univ ⊢Π)) ⊢ℕ ⊢G
       (≅-univ (≅ₜ-Π-cong (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) (λ abs → ⊥-elim (!≢% abs)) ⊢ℕ
                 (≅ₜ-ℕrefl ⊢Γ) (≅ₜ-ℕrefl ⊢Γℕ)))
       (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ [ℕ])
       [G] G-ext

record EquivRed : Set₁ where
  field
    [fwd] : ∀ {Γ equiv} (⊢Γ : ⊢ Γ) → equiv ∈ₗ equivs
          → let [Π] = Πℕℕ ⊢Γ
            in Γ ⊩⟨ ι ⁰ ⟩ emb_oterm_term (Eq.Equiv.fwd equiv)
                 ∷ Π ℕ ^ ! ° ⁰ ▹ ℕ ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / [Π]
    [bwd] : ∀ {Γ equiv} (⊢Γ : ⊢ Γ) → equiv ∈ₗ equivs
          → let [Π] = Πℕℕ ⊢Γ
            in Γ ⊩⟨ ι ⁰ ⟩ emb_oterm_term (Eq.Equiv.bwd equiv)
                 ∷ Π ℕ ^ ! ° ⁰ ▹ ℕ ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / [Π]
