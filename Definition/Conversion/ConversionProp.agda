{-# OPTIONS --safe #-}

import Definition.Equiv as E
module Definition.Conversion.ConversionProp (equiv : E.Equiv) where

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.RedSteps equiv
open import Definition.Typed.Properties equiv
open import Definition.Conversion equiv
open import Definition.Conversion.Stability equiv
open import Definition.Conversion.StabilityProp equiv
open import Definition.Conversion.Conversion equiv
open import Definition.Conversion.ConvSize equiv
open import Definition.Conversion.Soundness equiv
open import Definition.Typed.Consequences.Syntactic equiv
open import Definition.Typed.Consequences.Injectivity equiv
open import Definition.Typed.Consequences.Equality equiv
open import Definition.Typed.Consequences.Reduction equiv

open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Nat as Nat

sizeSubst-gen :  ∀ {A a b}
              → (P : A → Set)
              → (size : ∀ {a} → P a → Nat)
              → (t : P a)
              → (e : a PE.≡ b)
              → size (PE.subst P e t) PE.≡ size t
sizeSubst-gen _ _ _ PE.refl = PE.refl              

mutual

  -- Conversion of algorithmic equality.
  convConv↑TermSize : ∀ {t u A B Γ Δ l}
                → (Γ≡Δ : ⊢ Γ ≡ Δ)
                → (A≡B : Γ ⊢ A ≡ B ^ [ ! , l ])
                → (t~u : Γ ⊢ t [conv↑] u ∷ A ^ l)
                → sizeConv↑Term (convConv↑Term Γ≡Δ A≡B t~u) PE.≡ sizeConv↑Term t~u
  convConv↑TermSize Γ≡Δ A≡B ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let ⊢B , _ = syntacticEqTerm (soundnessConv↓Term t<>u)
        eq = convConv↓TermSize Γ≡Δ _ _ t<>u
    in PE.cong 1+ eq

  convConv↓TermSize : ∀ {t u A B Γ Δ l}
                → (Γ≡Δ : ⊢ Γ ≡ Δ)
                → (A≡B : Γ ⊢ A ≡ B ^ [ ! , l ])
                → (whnfB : Whnf B)
                → (t~u : Γ ⊢ t [conv↓] u ∷ A ^ l)
                → sizeConv↓Term (convConv↓Term Γ≡Δ A≡B whnfB t~u) PE.≡ sizeConv↓Term t~u
  convConv↓TermSize Γ≡Δ A≡B whnfB (U-refl x x₁) rewrite U≡A-whnf A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (ne x) rewrite U≡A-whnf A≡B whnfB = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  convConv↓TermSize Γ≡Δ A≡B whnfB (ℕ-refl x) rewrite U≡A-whnf A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (Empty-refl x) rewrite U≡A-whnf A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (Π-cong lΠ rF lF lG l< l<' x x₁ x₂) rewrite U≡A-whnf A≡B whnfB = PE.cong₂ (λ n m → 1 + (n + m))
    (stabilitySizeConv↑Term Γ≡Δ x₁)
    (stabilitySizeConv↑Term (Γ≡Δ ∙ refl x) x₂)
  convConv↓TermSize Γ≡Δ A≡B whnfB (Id-cong x x₁ x₂) rewrite U≡A-whnf A≡B whnfB = PE.cong₃ (λ n m k → 1 + (n + m + k))
    (stabilitySizeConv↑Term Γ≡Δ x)
    (stabilitySizeConv↑Term Γ≡Δ x₁)
    (stabilitySizeConv↑Term Γ≡Δ x₂)
  convConv↓TermSize Γ≡Δ A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  convConv↓TermSize Γ≡Δ A≡B whnfB (ne-ins t u x x₁) with ne≡A x A≡B whnfB
  convConv↓TermSize Γ≡Δ A≡B whnfB (ne-ins t u x x₁) | B , neB , PE.refl =
    PE.cong 1+ (stabilitySize~↓! Γ≡Δ x₁)
  convConv↓TermSize Γ≡Δ A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    PE.cong 1+ (stabilitySizeConv↑Term Γ≡Δ x)
  convConv↓TermSize Γ≡Δ A≡B whnfB (η-eq l< l<' x x₁ x₂ y y₁ x₃) =
    let F′ , G′ , eqΠ = Π≡A A≡B whnfB
        A≡B' = PE.subst (λ X → _ ⊢ _ ≡ X ^ _) eqΠ A≡B
        F≡F′ , rF≡rF′ , _ , _ , G≡G′ = injectivity A≡B'
    in PE.trans (sizeSubst-gen (λ X → _ ⊢ _ [conv↓] _ ∷ X ^ _) sizeConv↓Term _ (PE.sym (proj₂ (proj₂ (Π≡A A≡B whnfB)))))
                (PE.cong 1+ (convConv↑TermSize (Γ≡Δ ∙ F≡F′) G≡G′ x₃)) 
