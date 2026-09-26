import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.ProofIrrelevance (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}
open import Definition.Untyped senv equivs as U hiding (wk)
open import Definition.Untyped.Properties senv equivs using (wkSingleSubstId)
open import Definition.Typed senv equivs
open import Definition.Typed.Weakening senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.Properties senv equivs
open import Definition.LogicalRelation.Substitution senv equivs
open import Tools.Product
open import Tools.Unit
open import Tools.Empty
open import Tools.Nat
import Tools.PropositionalEquality as PE
~-quasirefl : ∀ {Γ n n′ A r} → Γ ⊢ n ~ n′ ∷ A ^ r → Γ ⊢ n ~ n ∷ A ^ r
~-quasirefl p = ~-trans p (~-sym p)

≅-quasirefl : ∀ {Γ n n′ A r} → Γ ⊢ n ≅ n′ ∷ A ^ r → Γ ⊢ n ≅ n ∷ A ^ r
≅-quasirefl p = ≅ₜ-trans p (≅ₜ-sym p)

proof-irrelevanceRel : ∀ {Γ A t u l l′} ([A] : Γ ⊩⟨ l ⟩ A ^ [ % , l′ ])
                   → Γ ⊩⟨ l ⟩ t ∷ A ^ [ % , l′ ] / [A]
                   → Γ ⊩⟨ l ⟩ u ∷ A ^ [ % , l′ ] / [A]
                   → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ % , l′ ] / [A]
proof-irrelevanceRel (Emptyᵣ x)
                   (Emptyₜ (ne ⊢t))
                   (Emptyₜ (ne ⊢t₁)) = Emptyₜ₌ (ne ⊢t ⊢t₁)

proof-irrelevanceRel (ne x)
                   (neₜ ⊢t)
                   (neₜ ⊢t₁) =
                   neₜ₌ ⊢t  ⊢t₁
proof-irrelevanceRel {Γ} {l = l} (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) [f] [f₁] =
  [f] , [f₁]
proof-irrelevanceRel {Γ} {l = l} (Idᵣ′ F G _ _ D ⊢F ⊢G _ A≡A) [f] [f₁] =
  [f] , [f₁]

proof-irrelevanceRel (emb emb< [A]) [t] [u] = proof-irrelevanceRel [A] [t] [u]
proof-irrelevanceRel (emb ∞< [A]) [t] [u] = proof-irrelevanceRel [A] [t] [u]

proof-irrelevanceᵛ : ∀ {Γ A t u l l′} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ % , l′ ] / [Γ])
                   → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ [ % , l′ ] / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ u ∷ A ^ [ % , l′ ] / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ [ % , l′ ] / [Γ] / [A]
proof-irrelevanceᵛ [Γ] [A] [t] [u] {σ = σ} ⊢Δ [σ] =
  proof-irrelevanceRel (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))


validityIrr : ∀ {l A t Γ l'} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ % , l' ] / [Γ])
                (⊢t : ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Δ ⊢ subst σ t ∷ subst σ A ^ [ % , l' ]) → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ [ % , l' ] / [Γ] / [A]
validityIrr [Γ] [A] ⊢t {Δ} {σ} ⊢Δ [σ] =
  let [Aσ] = proj₁ ([A] ⊢Δ [σ])
      [tσ] = logRelIrr [Aσ] (⊢t ⊢Δ [σ])
      -- [tσ] = proj₁ ([t] ⊢Δ [σ])
  in  logRelIrr [Aσ] (⊢t ⊢Δ [σ]) ,
      λ [σ′] [σ≡σ′] → let [Aσ′] = proj₁ ([A] ⊢Δ [σ′])
                          [tσ′] = logRelIrr [Aσ′] (⊢t ⊢Δ [σ′])
                          [Aσ≡σ′] = proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]
                      in logRelIrrEq [Aσ] (⊢t ⊢Δ [σ]) (escapeTerm [Aσ] (convTerm₂ [Aσ] [Aσ′] [Aσ≡σ′] [tσ′]))
