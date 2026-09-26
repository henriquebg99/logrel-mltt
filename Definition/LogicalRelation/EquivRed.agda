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

open import Definition.Untyped senv equivs hiding (wk)
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

ΠIndInd : ∀ {Γ} i j → (⊢Γ : ⊢ Γ) →
  Γ ⊩⟨ ι ⁰ ⟩ Π Ind i ^ ! ° ⁰ ▹ Ind j ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
ΠIndInd {Γ} i j ⊢Γ =
  let ⊢Ind = univ (Indⱼ ⊢Γ)
      [Ind] = Indᵣ (idRed:*: ⊢Ind)
      ⊢ΓInd = _∙_ ⊢Γ ⊢Ind
      ⊢G = univ (Indⱼ ⊢ΓInd)
      ⊢Π = Πⱼ (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ (Indⱼ ⊢Γ) ▹ (Indⱼ ⊢ΓInd)
      [G] : ∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
          → Δ ⊩⟨ ι ⁰ ⟩ Ind j ^ [ ! , ι ⁰ ]
      [G] [ρ] ⊢Δ [a] = Indᵣ (idRed:*: (univ (Indⱼ ⊢Δ)))
      G-ext : ∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
            → ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
            → ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
            → Δ ⊩⟨ ι ⁰ ⟩ Ind j ≡ Ind j ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [a]
      G-ext [ρ] ⊢Δ [a] [b] [a≡b] = reflEq ([G] [ρ] ⊢Δ [a])
  in Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) (Ind i) (Ind j) (idRed:*: (univ ⊢Π)) ⊢Ind ⊢G
       (≅-univ (≅ₜ-Π-cong (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) (λ abs → ⊥-elim (!≢% abs)) ⊢Ind
                 (≅ₜ-Indrefl ⊢Γ) (≅ₜ-Indrefl ⊢ΓInd)))
       (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ [Ind])
       [G] G-ext

-- The functions of every equivalence of [equivs] are reducible
record EquivRed : Set₁ where
  field
    [fwd] : ∀ {Γ equiv} (⊢Γ : ⊢ Γ) → equiv ∈ₗ equivs
          → let [Π] = ΠIndInd (Eq.Equiv.indA equiv) (Eq.Equiv.indB equiv) ⊢Γ
            in Γ ⊩⟨ ι ⁰ ⟩ emb_oterm_term (Eq.fwdₒ equiv)
                 ∷ Π Ind (Eq.Equiv.indA equiv) ^ ! ° ⁰ ▹ Ind (Eq.Equiv.indB equiv) ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / [Π]
    [bwd] : ∀ {Γ equiv} (⊢Γ : ⊢ Γ) → equiv ∈ₗ equivs
          → let [Π] = ΠIndInd (Eq.Equiv.indB equiv) (Eq.Equiv.indA equiv) ⊢Γ
            in Γ ⊩⟨ ι ⁰ ⟩ emb_oterm_term (Eq.bwdₒ equiv)
                 ∷ Π Ind (Eq.Equiv.indB equiv) ^ ! ° ⁰ ▹ Ind (Eq.Equiv.indA equiv) ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / [Π]
    -- The forward function of the equivalence between two inductives with the
    -- same representative (a composite of the equivalences of [equivs])
    [repr-fwd] : ∀ {Γ i j} (⊢Γ : ⊢ Γ) (H : reprInd i PE.≡ reprInd j)
               → Γ ⊩⟨ ι ⁰ ⟩ emb_oterm_term (Eq.fwdₒ (Eq.repr-equiv equivs i j H))
                   ∷ Π Ind i ^ ! ° ⁰ ▹ Ind j ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / ΠIndInd i j ⊢Γ
