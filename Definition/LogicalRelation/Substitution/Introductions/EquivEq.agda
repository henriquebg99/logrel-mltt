import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.EquivEq (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.LogicalRelation.Properties.Escape senv equivs
open import Definition.LogicalRelation.Substitution senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Id senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Universe senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Ind senv equivs
open import Definition.LogicalRelation.Substitution.MaybeEmbed senv equivs
open import Definition.LogicalRelation.Substitution.ProofIrrelevance senv equivs
open import Tools.Product
open import Tools.List using (nth)
open import Tools.Maybe using (just)
import Tools.PropositionalEquality as PE
-- Validity of the witness of the n-th equivalence of [equivs].
equivEqᵛ : ∀ {Γ n e}
  → ([Γ] : ⊩ᵛ Γ)
  → nth equivs n PE.≡ just e
  → let [U0] = maybeEmbᵛ {A = U ⁰} [Γ] (Uᵛ emb< [Γ])
        [A]  = maybeEmbTermᵛ {A = U ⁰} {t = Ind (E.Equiv.indA e)} [Γ] [U0] (Indᵗᵛ [Γ])
        [B]  = maybeEmbTermᵛ {A = U ⁰} {t = Ind (E.Equiv.indB e)} [Γ] [U0] (Indᵗᵛ [Γ])
        [Id] = Idᵛ {A = U ⁰} {t = Ind (E.Equiv.indA e)} {u = Ind (E.Equiv.indB e)} [Γ] [U0] [A] [B]
    in Γ ⊩ᵛ⟨ ∞ ⟩ equiv-eq n ∷ Id (U ⁰) (Ind (E.Equiv.indA e)) (Ind (E.Equiv.indB e)) ^ [ % , ι ⁰ ] / [Γ] / [Id]

equivEqᵛ {Γ} {n} {e} [Γ] eq =
  let [U0] = maybeEmbᵛ {A = U ⁰} [Γ] (Uᵛ emb< [Γ])
      [A]  = maybeEmbTermᵛ {A = U ⁰} {t = Ind (E.Equiv.indA e)} [Γ] [U0] (Indᵗᵛ [Γ])
      [B]  = maybeEmbTermᵛ {A = U ⁰} {t = Ind (E.Equiv.indB e)} [Γ] [U0] (Indᵗᵛ [Γ])
      [Id] = Idᵛ {A = U ⁰} {t = Ind (E.Equiv.indA e)} {u = Ind (E.Equiv.indB e)} [Γ] [U0] [A] [B]
  in validityIrr {A = Id (U ⁰) (Ind (E.Equiv.indA e)) (Ind (E.Equiv.indB e))} {t = equiv-eq n} [Γ] [Id]
       λ ⊢Δ [σ] → equiv-eqⱼ ⊢Δ eq
