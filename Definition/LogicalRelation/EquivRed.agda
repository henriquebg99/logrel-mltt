-- We define a record with a witness that the forward function between two
-- inductive types with the same representative is reducible in the logical
-- relation, for an instance of the generic equality. It is the only
-- reducibility fact about the equivalences needed by the cast rules; the
-- instance is built in Definition.LogicalRelation.Fundamental.SimpleTerm.

{-# OPTIONS --safe #-}

import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.EquivRed (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
import Definition.Equiv senv as Eq
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}

open import Definition.Untyped senv equivs hiding (wk)
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.RedSteps senv equivs
import Definition.Typed.Weakening senv equivs as Twk
open Twk using (_∷_⊆_)
open import Definition.LogicalRelation senv swf equivs
open import Definition.LogicalRelation.Properties senv swf equivs
open import Definition.LogicalRelation.Irrelevance senv swf equivs
import Definition.LogicalRelation.Weakening senv swf equivs as Lwk

open import Tools.Product
open import Tools.List using (_∈ₗ_)
open import Tools.Empty using (⊥-elim)
import Tools.PropositionalEquality as PE

ΠIndInd : ∀ {Γ} i j → i ∈ₗ SI.indNames senv → j ∈ₗ SI.indNames senv → (⊢Γ : ⊢ Γ) →
  Γ ⊩⟨ ι ⁰ ⟩ Π Ind i ^ ! ° ⁰ ▹ Ind j ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
ΠIndInd {Γ} i j i∈ j∈ ⊢Γ =
  let ⊢Ind = univ (Indⱼ′ ⊢Γ i∈)
      [Ind] = Indᵣ (idRed:*: ⊢Ind)
      ⊢ΓInd = _∙_ ⊢Γ ⊢Ind
      ⊢G = univ (Indⱼ′ ⊢ΓInd j∈)
      ⊢Π = Πⱼ (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ (Indⱼ′ ⊢Γ i∈) ▹ (Indⱼ′ ⊢ΓInd j∈)
      [G] : ∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
          → Δ ⊩⟨ ι ⁰ ⟩ Ind j ^ [ ! , ι ⁰ ]
      [G] [ρ] ⊢Δ [a] = Indᵣ (idRed:*: (univ (Indⱼ′ ⊢Δ j∈)))
      G-ext : ∀ {ρ Δ a b}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
            → ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
            → ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ Ind i ^ [ ! , ι ⁰ ] / Lwk.wk [ρ] ⊢Δ [Ind])
            → Δ ⊩⟨ ι ⁰ ⟩ Ind j ≡ Ind j ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [a]
      G-ext [ρ] ⊢Δ [a] [b] [a≡b] = reflEq ([G] [ρ] ⊢Δ [a])
  in Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) (Ind i) (Ind j) (idRed:*: (univ ⊢Π)) ⊢Ind ⊢G
       (≅-univ (≅ₜ-Π-cong (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) (λ abs → ⊥-elim (!≢% abs)) ⊢Ind
                 (≅ₜ-Indrefl ⊢Γ i∈) (≅ₜ-Indrefl ⊢ΓInd j∈)))
       (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ [Ind])
       [G] G-ext

record EquivRed : Set₁ where
  field
    -- The forward function of the equivalence between two inductives with the
    -- same representative (a composite of the equivalences of [equivs])
    [repr-fwd] : ∀ {Γ i j} (⊢Γ : ⊢ Γ) (i∈ : i ∈ₗ SI.indNames senv) (j∈ : j ∈ₗ SI.indNames senv)
                 (H : reprInd i PE.≡ reprInd j)
               → Γ ⊩⟨ ι ⁰ ⟩ emb-oterm (Eq.fwdₒ (Eq.repr-equiv equivs i j i∈ j∈ H))
                   ∷ Π Ind i ^ ! ° ⁰ ▹ Ind j ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / ΠIndInd i j i∈ j∈ ⊢Γ
