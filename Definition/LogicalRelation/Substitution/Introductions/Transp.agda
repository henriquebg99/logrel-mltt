import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.Transp (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}
open import Definition.Untyped senv equivs as U hiding (wk)
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.Weakening senv equivs as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps senv equivs
open import Definition.LogicalRelation senv swf equivs
open import Definition.LogicalRelation.ShapeView senv swf equivs
open import Definition.LogicalRelation.Irrelevance senv swf equivs as I
open import Definition.LogicalRelation.Weakening senv swf equivs
open import Definition.LogicalRelation.Properties senv swf equivs
open import Definition.LogicalRelation.Application senv swf equivs
open import Definition.LogicalRelation.Substitution senv swf equivs
open import Definition.LogicalRelation.Substitution.Properties senv swf equivs
open import Definition.LogicalRelation.Substitution.Irrelevance senv swf equivs as S
open import Definition.LogicalRelation.Substitution.Reflexivity senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Fst senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Pi senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Lambda senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Application senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Cast senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Id senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst senv swf equivs
open import Definition.LogicalRelation.Substitution.MaybeEmbed senv swf equivs
open import Definition.LogicalRelation.Substitution.Escape senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Universe senv swf equivs
open import Definition.LogicalRelation.Substitution.Reduction senv swf equivs
open import Definition.LogicalRelation.Substitution.Weakening senv swf equivs
open import Definition.LogicalRelation.Substitution.ProofIrrelevance senv swf equivs
open import Tools.Product
import Tools.PropositionalEquality as PE
IdSymᵗᵛ : ∀ {A l t u e Γ}
         ([Γ] : ⊩ᵛ Γ)
         ([U] : Γ ⊩ᵛ⟨ ∞ ⟩ U l ^ [ ! , next l ] / [Γ])
         ([AU] : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ U l ^ [ ! , next l ] / [Γ] / [U])
         ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
         ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
         ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
         ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ^ [ % , ι ⁰ ] / [Γ]) →
         ([Idinv] : Γ ⊩ᵛ⟨ ∞ ⟩ Id A u t ^ [ % , ι ⁰ ] / [Γ]) →
         ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id A t u ^ [ % , ι ⁰ ] / [Γ] / [Id] ) →
         Γ ⊩ᵛ⟨ ∞ ⟩ Idsym A t u e ∷ Id A u t  ^ [ % , ι ⁰ ] / [Γ] / [Idinv]
IdSymᵗᵛ {A} {l} {t} {u} {e} {Γ} [Γ] [U] [AU] [A] [t] [u] [Id] [Idinv] [e] = validityIrr {A = Id A u t} {t = Idsym A t u e} [Γ] [Idinv] λ {Δ} {σ} ⊢Δ [σ] →
  PE.subst (λ X → Δ ⊢ X ∷ subst σ (Id A u t) ^ [ % , ι ⁰ ] ) (PE.sym (subst-Idsym σ A t u e))
    (Idsymⱼ {A = subst σ A} {x = subst σ t} {y = subst σ u} (escapeTerm (proj₁ ([U] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([AU] ⊢Δ [σ])))
            (escapeTerm (proj₁ ([A] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))) 
            (escapeTerm (proj₁ ([A] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
            (escapeTerm (proj₁ ([Id] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ]))))

abstract 
  transpᵗᵛ : ∀ {A P l t s u e Γ}
           ([Γ] : ⊩ᵛ Γ)
           ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , l ] / [Γ])
           ([P] : Γ ∙ A ^ [ ! , l ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ % , ι ⁰ ] / (_∙_ {A = A} [Γ] [A]))
           ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , l ] / [Γ] / [A])
           ([s] : Γ ⊩ᵛ⟨ ∞ ⟩ s ∷ P [ t ]  ^ [ % , ι ⁰ ] / [Γ] / substS {A} {P} {t} [Γ] [A] [P] [t])
           ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , l ] / [Γ] / [A])
           ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ^ [ % , ι ⁰ ] / [Γ]) →
           ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id A t u ^ [ % , ι ⁰ ] / [Γ] / [Id] ) →
           Γ ⊩ᵛ⟨ ∞ ⟩ transp A P t s u e ∷ P [ u ]  ^ [ % , ι ⁰ ] / [Γ] / substS {A} {P} {u} [Γ] [A] [P] [u]
  transpᵗᵛ {A} {P} {l} {t} {s} {u} {e} {Γ} [Γ] [A] [P] [t] [s] [u] [Id] [e] =
    validityIrr {A = P [ u ]} {t = transp A P t s u e } [Γ] (substS {A} {P} {u} [Γ] [A] [P] [u]) λ {Δ} {σ} ⊢Δ [σ] →
    let [liftσ] = liftSubstS {F = A} [Γ] ⊢Δ [A] [σ]
        [A]σ = proj₁ ([A] {Δ} {σ} ⊢Δ [σ])
        [P[t]]σ = I.irrelevance′ (singleSubstLift P t) (proj₁ (substS {A} {P} {t} [Γ] [A] [P] [t] {Δ} {σ} ⊢Δ [σ]))
        X = transpⱼ (escape [A]σ) (escape (proj₁ ([P] {Δ ∙ subst σ A ^ [ ! , l ]} {liftSubst σ} (⊢Δ ∙ (escape [A]σ)) [liftσ])))
                            (escapeTerm [A]σ (proj₁ ([t] ⊢Δ [σ]))) (escapeTerm [P[t]]σ (I.irrelevanceTerm′ (singleSubstLift P t) PE.refl PE.refl (proj₁ (substS {A} {P} {t} [Γ] [A] [P] [t] {Δ} {σ} ⊢Δ [σ])) [P[t]]σ (proj₁ ([s] ⊢Δ [σ])))) 
                            (escapeTerm [A]σ (proj₁ ([u] ⊢Δ [σ]))) (escapeTerm (proj₁ ([Id] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ])))
    in PE.subst (λ X → Δ ⊢ transp (subst σ A) ( subst (liftSubst σ) P) (subst σ t) (subst σ s) (subst σ u) (subst σ e) ∷ X ^ [ % , ι ⁰ ] ) (PE.sym (singleSubstLift P u)) X
