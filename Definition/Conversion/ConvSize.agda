-- Algorithmic equality.

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.ConvSize (senv : SI.SEnv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Definition.Conversion senv equivs
open import Tools.List using (All₃; []ₐ; _∷ₐ_)
mutual
  -- Neutral equality.
  size~↑! : ∀ {t u A Γ l} → Γ ⊢ t ~ u ↑! A ^ l → Nat

  size~↑! (var-refl x x₁) = 1
  size~↑! (app-cong x x₁) = 1 + size~↓! x + size[genconv↑] x₁
  size~↑! (Emptyrec-cong x x₁) = 1 + sizeConv↑ x
  size~↑! (cast-cong x x₁ x₄ x₅ x₆) = 1 + size~↓! x + size~↓! x₁ + sizeConv↓Term x₄
  size~↑! (cast-refl x x₃ x₄) = 1 + size~↓! x + sizeConv↓Term x₃
  size~↑! (cast-refl' x x₃ x₄) = 1 + size~↓! x + sizeConv↓Term x₃
  size~↑! (cast-neΠ x x₁ x₂ x₃ x₄) = 1 + sizeConv↑Term x + size~↓! x₁ + sizeConv↑Term x₂
  size~↑! (cast-Π x x₁ x₂ x₃ x₄) = 1 + sizeConv↑Term x + size~↓! x₁ + sizeConv↑Term x₂
  size~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = 1 + sizeConv↑Term x + sizeConv↑Term x₁ + sizeConv↑Term x₂
  size~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = 1 + sizeConv↑Term x + sizeConv↑Term x₁ + sizeConv↑Term x₂
  size~↑! (IndRect-cong _ x x₁ x₂) = 1 + sizeConv↑ x + size~↓! x₁ + sizeConv↑TermAll x₂
  size~↑! (cast-neInd x x₁ x₂ x₃) = 1 + size~↓! x + sizeConv↑Term x₁
  size~↑! (cast-Ind x x₁ x₂ x₃) = 1 + size~↓! x + sizeConv↑Term x₁
  size~↑! (cast-IndΠ x x₁ x₂ x₃) = 1 + sizeConv↑Term x + sizeConv↑Term x₁
  size~↑! (cast-ΠInd x x₁ x₂ x₃) = 1 + sizeConv↑Term x + sizeConv↑Term x₁
  size~↑! (cast-IndInd x x₁ x₂ x₃) = 1 + sizeConv↑Term x₁
  
  size~↑ : ∀ {t u A Γ l} → Γ ⊢ t ~ u ↑ A ^ l → Nat
  size~↑ (~↑! x) = size~↑! x
  size~↑ (~↑% x) = 1

  size~↓! : ∀ {t u A Γ l} → Γ ⊢ t ~ u ↓! A ^ l → Nat
  size~↓! ([~] A D whnfB k~l) = 1+ (size~↑! k~l)
  
  sizeConv↑ : ∀ {A B Γ l} → Γ ⊢ A [conv↑] B ^ l → Nat
  sizeConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) = 1 + sizeConv↓ A′<>B′

  sizeConv↑Term : ∀ {t u A Γ l} → Γ ⊢ t [conv↑] u ∷ A ^ l → Nat
  sizeConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = 1 + sizeConv↓Term t<>u

  size[genconv↑] : ∀ {t u A Γ l} → Γ ⊢ t [genconv↑] u ∷ A ^ l → Nat
  size[genconv↑] {l = [ ! , l ]} X = sizeConv↑Term X
  size[genconv↑] {l = [ % , l ]} X = 1

  sizeConv↓Term : ∀ {t u A Γ l} → Γ ⊢ t [conv↓] u ∷ A ^ l → Nat
  sizeConv↓Term (U-refl x x₁) = 1
  sizeConv↓Term (ne x) = 1 + size~↓! x
  sizeConv↓Term (Empty-refl x) = 1
  sizeConv↓Term (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = 1 + sizeConv↑Term x₇ + sizeConv↑Term x₈
  sizeConv↓Term (Id-cong x x₁ x₂) = 1 + sizeConv↑Term x + sizeConv↑Term x₁ + sizeConv↑Term x₂
  sizeConv↓Term (Ind-ins x) = 1 + size~↓! x
  sizeConv↓Term (ne-ins x x₁ x₂ x₃) = 1 + size~↓! x₃ 
  sizeConv↓Term (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = 1 + sizeConv↑Term x₇
  sizeConv↓Term (Ind-refl x _) = 1
  sizeConv↓Term (ctr-cong x x₁ x₂ x₃) = 1 + sizeConv↑TermAll x₃

  sizeConv↑TermAll : ∀ {As args args' Γ l} → All₃ (λ a a' A → Γ ⊢ a [conv↑] a' ∷ A ^ l) args args' As → Nat
  sizeConv↑TermAll []ₐ = 0
  sizeConv↑TermAll (p ∷ₐ ps) = sizeConv↑Term p + sizeConv↑TermAll ps

  sizeConv↓ : ∀ {A B Γ l} → Γ ⊢ A [conv↓] B ^ l → Nat
  sizeConv↓ (U-refl x x₁) = 1
  sizeConv↓ (univ x) = 1 + sizeConv↓Term x
