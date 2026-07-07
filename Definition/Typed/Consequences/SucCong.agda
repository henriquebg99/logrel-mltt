{-# OPTIONS --safe #-}

import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
import Definition.LogicalRelation.EquivRed as ERd
module Definition.Typed.Consequences.SucCong
  (equiv : E.Equiv)
  (equivRed : forall (eqrel : ER.EqRelSet equiv) → ERd.EquivRed equiv eqrel) where

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.Weakening equiv
open import Definition.Typed.Properties equiv
open import Definition.Typed.EqRelInstance equiv
open import Definition.Typed.Consequences.Syntactic equiv equivRed
open import Definition.Typed.Consequences.Substitution equiv equivRed

open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)


-- Congurence of the type of the successor case in natrec.
sucCong : ∀ {F G lF Γ} → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ≡ G ^ [ ! , ι lF ]
        → Γ ⊢ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ !
            ≡ Π ℕ ^ ! ° ⁰ ▹ (G ^ ! ° lF ▹▹ G [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ [ ! , ι lF ]
sucCong F≡G with wfEq F≡G
sucCong {lF = lF} F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , _ = syntacticEq F≡G
  in  univ (Π-cong (λ x → (⁰min lF) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢ℕ (refl (un-univ ⊢ℕ))
             (Π-cong (λ x → (≡is≤ PE.refl) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢F (un-univ≡ F≡G)
                     (wkEqTerm (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
                               (un-univ≡ (subst↑TypeEq F≡G
                                                       (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))))))

-- Congurence of the type of the successor case in natrec2.
suc2Cong : ∀ {F G lF Γ} → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ F ≡ G ^ [ ! , ι lF ]
         → Γ ⊢ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ !
             ≡ Π ℕ2 ^ ! ° ⁰ ▹ (G ^ ! ° lF ▹▹ G [ suc2 (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ [ ! , ι lF ]
suc2Cong F≡G with wfEq F≡G
suc2Cong {lF = lF} F≡G | ⊢Γ ∙ ⊢ℕ2 =
  let ⊢F , _ = syntacticEq F≡G
  in  univ (Π-cong (λ x → (⁰min lF) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢ℕ2 (refl (un-univ ⊢ℕ2))
             (Π-cong (λ x → (≡is≤ PE.refl) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢F (un-univ≡ F≡G)
                     (wkEqTerm (step id) (⊢Γ ∙ ⊢ℕ2 ∙ ⊢F)
                               (un-univ≡ (subst↑TypeEq F≡G
                                                       (refl (suc2ⱼ (var (⊢Γ ∙ ⊢ℕ2) here))))))))
