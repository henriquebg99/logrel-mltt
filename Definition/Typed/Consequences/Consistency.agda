{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.Consistency (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where

open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.EqRelInstance senv swf equivs
open import Definition.LogicalRelation senv swf equivs
open import Definition.LogicalRelation.Irrelevance senv swf equivs
open import Definition.LogicalRelation.ShapeView senv swf equivs
open import Definition.LogicalRelation.Fundamental.Reducibility senv swf equivs

open import Tools.Empty
open import Tools.Product
import Tools.PropositionalEquality as PE


ctr≢ctr″ : ∀ {Γ i j j′ ts us a b} → j PE.≢ j′
         → a PE.≡ ctr i j ts → b PE.≡ ctr i j′ us
         → [Inductive]-prop Γ i a b → ⊥
ctr≢ctr″ j≢j′ a≡ b≡ (ctrᵣ _ _ _ _) =
  j≢j′ (PE.trans (PE.sym (proj₁ (proj₂ (ctr-PE-injectivity a≡))))
                 (proj₁ (proj₂ (ctr-PE-injectivity b≡))))
ctr≢ctr″ j≢j′ a≡ b≡ (ne (neNfₜ₌ neK neM k≡m)) = ctr≢ne neK (PE.sym a≡)

ctr≢ctr′ : ∀ {Γ l i j j′ ts us} → j PE.≢ j′ → ([Ind] : Γ ⊩⟨ l ⟩Ind Ind i ^ i)
         → Γ ⊩⟨ l ⟩ ctr i j ts ≡ ctr i j′ us ∷ Ind i ^ [ ! , ι ⁰ ] / Ind-intr [Ind] → ⊥
ctr≢ctr′ j≢j′ (noemb x) (Indₜ₌ k k′ d d′ k≡k′ prop) =
  ctr≢ctr″ j≢j′ (PE.sym (whnfRed*Term (redₜ d) ctrₙ)) (PE.sym (whnfRed*Term (redₜ d′) ctrₙ)) prop
ctr≢ctr′ j≢j′ (emb emb< [Ind]) n = ctr≢ctr′ j≢j′ [Ind] n
ctr≢ctr′ j≢j′ (emb ∞< [Ind]) n = ctr≢ctr′ j≢j′ [Ind] n

-- Distinct constructors of an inductive type cannot be judgmentally equal
-- (for natural numbers, zero cannot be judgmentally equal to one).
ctr≢ctr : ∀ {Γ i j j′ ts us} → j PE.≢ j′
        → Γ ⊢ ctr i j ts ≡ ctr i j′ us ∷ Ind i ^ [ ! , ι ⁰ ] → ⊥
ctr≢ctr j≢j′ c≡c′ =
  let [Ind] , [c≡c′] = reducibleEqTerm c≡c′
  in  ctr≢ctr′ j≢j′ (Ind-elim [Ind]) (irrelevanceEqTerm [Ind] (Ind-intr (Ind-elim [Ind])) [c≡c′])
