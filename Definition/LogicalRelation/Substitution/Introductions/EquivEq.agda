import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.EquivEq (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}
open import Definition.Untyped senv
open import Definition.Typed senv equivs
open import Definition.LogicalRelation.Properties.Escape senv equivs
open import Definition.LogicalRelation.Substitution senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Id senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Universe senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Nat senv equivs
open import Definition.LogicalRelation.Substitution.MaybeEmbed senv equivs
open import Definition.LogicalRelation.Substitution.ProofIrrelevance senv equivs
open import Tools.Product
-- Validity of the equivalence witness between ℕ and ℕ.
equivEqᵛ : ∀ {Γ}
  → ([Γ] : ⊩ᵛ Γ)
  → let [U0] = maybeEmbᵛ {A = U ⁰} [Γ] (Uᵛ emb< [Γ])
        [ℕ]  = maybeEmbTermᵛ {A = U ⁰} {t = ℕ} [Γ] [U0] (ℕᵗᵛ [Γ])
        [Id] = Idᵛ {A = U ⁰} {t = ℕ} {u = ℕ} [Γ] [U0] [ℕ] [ℕ]
    in Γ ⊩ᵛ⟨ ∞ ⟩ equiv-eq ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ] / [Γ] / [Id]

equivEqᵛ {Γ} [Γ] =
  let [U0] = maybeEmbᵛ {A = U ⁰} [Γ] (Uᵛ emb< [Γ])
      [ℕ]  = maybeEmbTermᵛ {A = U ⁰} {t = ℕ} [Γ] [U0] (ℕᵗᵛ [Γ])
      [Id] = Idᵛ {A = U ⁰} {t = ℕ} {u = ℕ} [Γ] [U0] [ℕ] [ℕ]
  in validityIrr {A = Id (U ⁰) ℕ ℕ} {t = equiv-eq} [Γ] [Id]
       λ ⊢Δ [σ] → equiv-eqⱼ ⊢Δ
