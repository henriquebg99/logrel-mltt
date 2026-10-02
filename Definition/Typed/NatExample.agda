-- Natural numbers as an instance of the generic inductive types:
-- the eliminator IndRect specialises to the usual natrec.

{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.SUntyped as SU
import Definition.Equiv as E
import Tools.List as TL
open import Tools.List using (_∈ₗ_)
import Tools.PropositionalEquality as PE

module Definition.Typed.NatExample (senv : SI.SEnv) (equivs : E.Equivs senv)
  (nat_ind : SU.SInd)
  (nat∈ : nat_ind ∈ₗ senv)
  (nat_ctrs : SU.SInd.ctrArgsTypes nat_ind
              PE.≡ TL.[] TL.∷ (SU.Ind (SU.SInd.name nat_ind) TL.∷ TL.[]) TL.∷ TL.[])
  where

open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty
open import Tools.List using (map; length)
open import Tools.Nat using (_≟_; 1+)
open import Tools.Nullary using (yes; no)
open TL using (range)

natName : Nat
natName = SU.SInd.name nat_ind

Zero : Term
Zero = ctr natName 0 TL.[]

-- Method type for O: just P [ Zero ].
nat-method-ty-Zero : ∀ P rG lG →
  indRectBranchTy natName 0 TL.[] P rG lG PE.≡ P [ Zero ]
nat-method-ty-Zero P rG lG = PE.refl

≟-refl : (n : Nat) → (n ≟ n) PE.≡ yes PE.refl
≟-refl 0 = PE.refl
≟-refl (1+ n) with n ≟ n | ≟-refl n
... | yes PE.refl | PE.refl = PE.refl
... | no p | _ = ⊥-elim (p PE.refl)

-- Method type for S: Π (n : Ind). Π (ih : P [ n ]). P [ S n ].
nat-method-ty-Succ : ∀ P rG lG →
  indRectBranchTy natName 1 (SU.Ind natName TL.∷ TL.[]) P rG lG PE.≡
  Π Ind natName ^ ! ° ⁰ ▹
    (Π (P [ var 0 ]↑) ^ rG ° lG ▹
       P [ ctr natName 1 (var 1 TL.∷ TL.[]) ]↑^ 2
     ° lG ° lG ^ rG)
  ° lG ° lG ^ rG
nat-method-ty-Succ P rG lG rewrite ≟-refl natName = PE.refl

indRectBranchTyList-nat : ∀ P rG lG →
  indRectBranchTyList nat_ind P rG lG PE.≡
  (P [ Zero ]) TL.∷
  (Π Ind natName ^ ! ° ⁰ ▹
    (Π (P [ var 0 ]↑) ^ rG ° lG ▹
       P [ ctr natName 1 (var 1 TL.∷ TL.[]) ]↑^ 2
     ° lG ° lG ^ rG)
   ° lG ° lG ^ rG) TL.∷
  TL.[]
indRectBranchTyList-nat P rG lG =
  PE.trans
    (PE.cong
      (λ Tss → map (λ jTs → indRectBranchTy natName (proj₁ jTs) (proj₂ jTs) P rG lG)
                   (TL.zip (range (length Tss)) Tss))
      nat_ctrs)
    (PE.cong₂ TL._∷_ (nat-method-ty-Zero P rG lG)
      (PE.cong (λ A → A TL.∷ TL.[] ) (nat-method-ty-Succ P rG lG)))

⊢-nat-IndRect : ∀ {Γ P rG lG t z s} →
  (rG PE.≡ % → lG PE.≡ ⁰) →
  Γ ∙ Ind natName ^ [ ! , ι ⁰ ] ⊢ P ^ [ rG , ι lG ] →
  Γ ⊢ t ∷ Ind natName ^ [ ! , ι ⁰ ] →
  Γ ⊢ z ∷ (P [ Zero ]) ^ [ rG , ι lG ] →
  Γ ⊢ s ∷
    Π Ind natName ^ ! ° ⁰ ▹
      (Π (P [ var 0 ]↑) ^ rG ° lG ▹
         P [ ctr natName 1 (var 1 TL.∷ TL.[]) ]↑^ 2
       ° lG ° lG ^ rG)
    ° lG ° lG ^ rG
    ^ [ rG , ι lG ] →
  Γ ⊢ IndRect natName lG P t (z TL.∷ s TL.∷ TL.[]) ∷ P [ t ] ^ [ rG , ι lG ]
⊢-nat-IndRect {Γ} {P} {rG} {lG} {t} {z} {s} abs ⊢P ⊢t ⊢z ⊢s =
  IndRectⱼ abs nat∈ ⊢P ⊢t
    (PE.subst (λ As → Γ ⊢All (z TL.∷ s TL.∷ TL.[]) ∷ As ^ [ rG , ι lG ])
      (PE.sym (indRectBranchTyList-nat P rG lG))
      (consⱼ ⊢z (consⱼ ⊢s εⱼ)))
