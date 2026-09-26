import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Properties.MaybeEmb (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.LogicalRelation senv equivs
import Tools.PropositionalEquality as PE
-- Any level can be embedded into the highest level.
maybeEmb : ∀ {l A r Γ}
         → Γ ⊩⟨ l ⟩ A ^ r
         → Γ ⊩⟨ ∞ ⟩ A ^ r
maybeEmb {ι ⁰} [A] = emb ∞< (emb emb< [A])
maybeEmb {ι ¹} [A] = emb ∞< [A]
maybeEmb {∞} [A] = [A]

-- Any level can be embedded into the highest level.
maybeEmbTerm : ∀ {l A t r Γ}
         → ([A] : Γ ⊩⟨ l ⟩ A ^ r)
         → Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A]
         → Γ ⊩⟨ ∞ ⟩ t ∷ A ^ r / maybeEmb [A]
maybeEmbTerm {ι ⁰} [A] [t] = [t]
maybeEmbTerm {ι ¹} [A] [t] = [t]
maybeEmbTerm {∞} [A] [t] = [t]

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l l' A r Γ}
          → l ≤ l'
          → Γ ⊩⟨ ι l ⟩ A ^ r
          → Γ ⊩⟨ ι l' ⟩ A ^ r
maybeEmb′ (<is≤ 0<1) [A] = emb emb< [A]
maybeEmb′ (≡is≤ PE.refl) [A] = [A]

maybeEmb″ : ∀ {l A r Γ}
         → Γ ⊩⟨ ι ⁰ ⟩ A ^ r
         → Γ ⊩⟨ l ⟩ A ^ r
maybeEmb″ {ι ⁰} [A] = [A]
maybeEmb″ {ι ¹} [A] = emb emb< [A]
maybeEmb″ {∞} [A] = emb ∞< (emb emb< [A])
