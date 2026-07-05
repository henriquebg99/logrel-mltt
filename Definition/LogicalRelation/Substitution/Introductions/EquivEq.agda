{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Substitution.Introductions.EquivEq (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.LogicalRelation.Properties.Escape equiv
open import Definition.LogicalRelation.Substitution equiv
open import Definition.LogicalRelation.Substitution.Introductions.Id equiv
open import Definition.LogicalRelation.Substitution.Introductions.Universe equiv
open import Definition.LogicalRelation.Substitution.Introductions.Nat equiv
open import Definition.LogicalRelation.Substitution.Introductions.Nat2 equiv
open import Definition.LogicalRelation.Substitution.MaybeEmbed equiv
open import Definition.LogicalRelation.Substitution.ProofIrrelevance equiv

open import Tools.Product

-- Validity of the equivalence witness between ℕ and ℕ2.
equivEqᵛ : ∀ {Γ}
  → ([Γ] : ⊩ᵛ Γ)
  → let [U0] = maybeEmbᵛ {A = U ⁰} [Γ] (Uᵛ emb< [Γ])
        [ℕ]  = maybeEmbTermᵛ {A = U ⁰} {t = ℕ} [Γ] [U0] (ℕᵗᵛ [Γ])
        [ℕ2] = maybeEmbTermᵛ {A = U ⁰} {t = ℕ2} [Γ] [U0] (ℕ2ᵗᵛ [Γ])
        [Id] = Idᵛ {A = U ⁰} {t = ℕ} {u = ℕ2} [Γ] [U0] [ℕ] [ℕ2]
    in Γ ⊩ᵛ⟨ ∞ ⟩ equiv-eq ∷ Id (U ⁰) ℕ ℕ2 ^ [ % , ι ⁰ ] / [Γ] / [Id]

equivEqᵛ {Γ} [Γ] =
  let [U0] = maybeEmbᵛ {A = U ⁰} [Γ] (Uᵛ emb< [Γ])
      [ℕ]  = maybeEmbTermᵛ {A = U ⁰} {t = ℕ} [Γ] [U0] (ℕᵗᵛ [Γ])
      [ℕ2] = maybeEmbTermᵛ {A = U ⁰} {t = ℕ2} [Γ] [U0] (ℕ2ᵗᵛ [Γ])
      [Id] = Idᵛ {A = U ⁰} {t = ℕ} {u = ℕ2} [Γ] [U0] [ℕ] [ℕ2]
  in validityIrr {A = Id (U ⁰) ℕ ℕ2} {t = equiv-eq} [Γ] [Id]
       λ ⊢Δ [σ] → equiv-eqⱼ ⊢Δ
