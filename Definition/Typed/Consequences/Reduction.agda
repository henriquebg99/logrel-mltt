{-# OPTIONS --safe #-}

import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
import Definition.LogicalRelation.EquivRed as ERd
module Definition.Typed.Consequences.Reduction
  (equiv : E.Equiv)
  (equivRed : forall (eqrel : ER.EqRelSet equiv) → ERd.EquivRed equiv eqrel) where

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.Typed.EqRelInstance equiv
open import Definition.LogicalRelation equiv 
open import Definition.LogicalRelation.Properties.Conversion equiv 
open import Definition.LogicalRelation.Fundamental.Reducibility equiv equivRed
import Tools.PropositionalEquality as PE

open import Tools.Product


-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A rA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ^ rA)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm′ (Uᵣ′ _ _ r l _ e d) = Univ r l , Uₙ , PE.subst (λ ll → _ ⊢ _ :⇒*: Univ r l ^ [ ! , ll ]) e d
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (ℕ2ᵣ D) = ℕ2 , ℕ2ₙ , D
whNorm′ (Emptyᵣ D) = sEmpty , Emptyₙ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Πᵣ {l = l} (Πᵣ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) = Π F ^ rF ° lF ▹ G ° lG ° l ^ ! , Πₙ , D
whNorm′ (Idᵣ′ A t u _ D ⊢F ⊢G _ A≡A) = Id A t u , Idₙ , D
whNorm′ (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) = Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % , Πₙ , D
whNorm′ (emb emb< [A]) = whNorm′ [A]
whNorm′ (emb ∞< [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A rA Γ} → Γ ⊢ A ^ rA → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm A = whNorm′ (reducible A)

-- whNorm-conv : ∀ {A rA Γ} → Γ ⊢ A ≡ B ^ rA → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
-- whNorm-conv A = whNorm′ (reducible A)


-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A Γ l lA} ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , lA ]) → Γ ⊩⟨ l ⟩ a ∷ A ^ [ ! , lA ] / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ lA
whNormTerm′ (Uᵣ′ _ _ r l _ e dU) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA ,
  conv:⇒*: (PE.subst (λ ll → _ ⊢ _ :⇒*: _ ∷ _ ^ ll) e d)
    (sym (subset* (red (PE.subst (λ ll → _ ⊢ _ :⇒*: Univ r l ^ [ ! , ll ]) e dU))))
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ℕ2ᵣ x) (ℕ2ₜ n d n≡n prop) =
  let natN = natural2 prop
  in  n , natural2Whnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ rF lF lG lF≤ lG≤  F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb emb< [A]) [a] = whNormTerm′ [A] [a]
whNormTerm′ (emb ∞< [A]) [a] = whNormTerm′ [A] [a]


-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A Γ lA} → Γ ⊢ a ∷ A ^ [ ! , lA ] → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ lA
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]
