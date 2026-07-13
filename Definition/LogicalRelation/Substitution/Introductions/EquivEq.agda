import Definition.Equiv as E
open import Definition.Typed.EqualityRelation
module Definition.LogicalRelation.Substitution.Introductions.EquivEq {{eqrel : EqRelSet}} where
open import Definition.Typed.EqualityRelation
open EqRelSet {{...}}
open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Nat2
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.ProofIrrelevance
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
