{-# OPTIONS --safe #-}

import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.IdRefl (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs 
open import Definition.LogicalRelation.Properties.Escape senv swf equivs
open import Definition.LogicalRelation.Substitution senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Id senv swf equivs
open import Definition.LogicalRelation.Substitution.ProofIrrelevance senv swf equivs
open import Tools.Product
Idreflᵛ : ∀{Γ A l t}
  → ([Γ] : ⊩ᵛ Γ)
  → ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
  → ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
  → let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
    in Γ ⊩ᵛ⟨ ∞ ⟩ Idrefl A t ∷ Id A t t ^ [ % , ι ⁰ ] / [Γ] / [Id]

Idreflᵛ {Γ} {A} {l} {t} [Γ] [A] [t]  =
  let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
  in validityIrr {A = Id A t t} {t = Idrefl A t} [Γ] [Id] λ ⊢Δ [σ] → Idreflⱼ (escapeTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])))

