{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
import Definition.LogicalRelation.EquivRed as ERd
module Definition.LogicalRelation.Substitution.Introductions.IdRefl (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} (equivRed : forall (eqrel : ER.EqRelSet equiv) → ERd.EquivRed equiv eqrel) where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.LogicalRelation.Properties.Escape equiv
open import Definition.LogicalRelation.Substitution equiv
open import Definition.LogicalRelation.Substitution.Introductions.Id equiv equivRed
open import Definition.LogicalRelation.Substitution.ProofIrrelevance equiv

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

