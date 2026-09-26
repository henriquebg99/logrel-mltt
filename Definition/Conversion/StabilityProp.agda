import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.StabilityProp (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.RedSteps senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.Conversion senv swf equivs
open import Definition.Conversion.ConvSize senv equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Definition.Typed.Consequences.Reduction senv swf equivs
open import Tools.Product
open import Tools.List using (All₂; []ₐ; _∷ₐ_)
import Tools.PropositionalEquality as PE
open import Tools.Nat as Nat
plus0 : ∀ {n : Nat} → (n + 0) PE.≡ n
plus0 {0} = PE.refl
plus0 {1+ n} = PE.cong 1+ plus0

mutual

  stabilitySize~↑! : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k ~ l ↑! A ^ lA)
              → size~↑! (stability~↑! Γ≡Δ t~u) PE.≡
                size~↑! t~u

  stabilitySize~↑! Γ≡Δ (var-refl x x₁) = PE.refl
  stabilitySize~↑! Γ≡Δ (app-cong {rF = !} x x₁) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁) 
  stabilitySize~↑! Γ≡Δ (app-cong {rF = %} x x₁) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             PE.refl
  stabilitySize~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) = PE.cong₄ (λ a b c d → 1+ (a + b + c + d))
             (stabilitySizeConv↑ _ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁)
             (stabilitySizeConv↑Term Γ≡Δ x₂)
             (stabilitySize~↓! Γ≡Δ x₃) 
  stabilitySize~↑! Γ≡Δ (Emptyrec-cong x x₁) = PE.cong (λ n → 1+ n) (stabilitySizeConv↑ Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-cong x x₁ x₂ _ _) =  PE.cong₃ (λ a b c → 1+ (a + b + c))
             (stabilitySize~↓! Γ≡Δ x) 
             (stabilitySize~↓! Γ≡Δ x₁)
             (stabilitySizeConv↓Term Γ≡Δ x₂)
  stabilitySize~↑! Γ≡Δ (cast-refl x x₁ _) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↓Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (castℕ-refl x x₁) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-refl' x x₁ _) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↓Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (castℕ-refl' x x₁) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (cast-neΠ a x x₁ x₂ x₃) = PE.cong₃ (λ a b c → 1+ (a + b + c))
             (stabilitySizeConv↑Term Γ≡Δ a)
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (cast-Π a x x₁ x₂ x₃) = PE.cong₃ (λ a b c → 1+ (a + b + c))
             (stabilitySizeConv↑Term Γ≡Δ a)
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (cast-Πℕ a x x₁ x₂) = PE.cong₂ (λ a b → 1+ (a + b)) (stabilitySizeConv↑Term Γ≡Δ a) (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-ℕΠ a x x₁ x₂) = PE.cong₂ (λ a b → 1+ (a + b)) (stabilitySizeConv↑Term Γ≡Δ a) (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-ΠΠ%! a b x x₁ x₂) = PE.cong₃ (λ a b c → 1+ (a + b + c))
             (stabilitySizeConv↑Term Γ≡Δ a)
             (stabilitySizeConv↑Term Γ≡Δ b)
             (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-ΠΠ!% a b x x₁ x₂) =  PE.cong₃ (λ a b c → 1+ (a + b + c))
             (stabilitySizeConv↑Term Γ≡Δ a)
             (stabilitySizeConv↑Term Γ≡Δ b)
             (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (IndRect-cong _ x x₁ x₂) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySizeConv↑ _ x)
             (stabilitySize~↓! Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) = PE.cong₂ (λ a b → 1+ (a + b))
             (stabilitySize~↓! Γ≡Δ x)
             (stabilitySizeConv↑Term Γ≡Δ x₁)
  stabilitySize~↑! Γ≡Δ (castInd-refl x x₁) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (castInd-refl' x x₁) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-IndΠ a x x₁ x₂) = PE.cong₂ (λ a b → 1+ (a + b)) (stabilitySizeConv↑Term Γ≡Δ a) (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-ΠInd a x x₁ x₂) = PE.cong₂ (λ a b → 1+ (a + b)) (stabilitySizeConv↑Term Γ≡Δ a) (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-Indℕ x x₁ x₂) = PE.cong 1+ (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-ℕInd x x₁ x₂) = PE.cong 1+ (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySize~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) = PE.cong 1+ (stabilitySizeConv↑Term Γ≡Δ x₁)

  stabilitySize~↓! : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k ~ l ↓! A ^ lA)
              → size~↓! (stability~↓! Γ≡Δ t~u) PE.≡
                size~↓! t~u

  stabilitySize~↓! Γ≡Δ t~u = PE.cong 1+ (stabilitySize~↑! Γ≡Δ (_⊢_~_↓!_^_.k~l t~u))

  stabilitySizeConv↓Term : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↓] l ∷ A ^ lA)
              → sizeConv↓Term (stabilityConv↓Term Γ≡Δ t~u) PE.≡
                sizeConv↓Term t~u
  stabilitySizeConv↓Term Γ≡Δ (U-refl x x₁) = PE.refl
  stabilitySizeConv↓Term Γ≡Δ (ne x) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  stabilitySizeConv↓Term Γ≡Δ (ℕ-refl x) = PE.refl
  stabilitySizeConv↓Term Γ≡Δ (Empty-refl x) = PE.refl
  stabilitySizeConv↓Term Γ≡Δ (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' F A<>B A<>B₁) = PE.cong₂ (λ a b → 1 + (a + b))
                  (stabilitySizeConv↑Term Γ≡Δ A<>B)
                  (stabilitySizeConv↑Term _ A<>B₁)
  stabilitySizeConv↓Term Γ≡Δ (Id-cong x x₁ x₂) = PE.cong₃ (λ a b c → 1+ (a + b + c))
             (stabilitySizeConv↑Term Γ≡Δ x) 
             (stabilitySizeConv↑Term Γ≡Δ x₁)
             (stabilitySizeConv↑Term Γ≡Δ x₂)
  stabilitySizeConv↓Term Γ≡Δ (ℕ-ins x) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  stabilitySizeConv↓Term Γ≡Δ (Ind-ins x) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  stabilitySizeConv↓Term Γ≡Δ (Ind-refl x) = PE.refl
  stabilitySizeConv↓Term Γ≡Δ (ne-ins x x₁ x₂ x₃) = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x₃)
  stabilitySizeConv↓Term Γ≡Δ (zero-refl x) = PE.refl
  stabilitySizeConv↓Term Γ≡Δ (suc-cong x) = PE.cong 1+ (stabilitySizeConv↑Term Γ≡Δ x)
  stabilitySizeConv↓Term Γ≡Δ (η-eq l< l<' F x x₁ y y₁ t<>u) = PE.cong 1+ (stabilitySizeConv↑Term _ t<>u)
  stabilitySizeConv↓Term Γ≡Δ (ctr-cong x x₁ x₂ x₃ x₄) = PE.cong 1+ (stabilityAll₂Size Γ≡Δ x₄)
    where
    stabilityAll₂Size : ∀ {args args' i Γ Δ}
                       → (Γ≡Δ : ⊢ Γ ≡ Δ)
                       → (ps : All₂ (λ a a' → Γ ⊢ a [conv↑] a' ∷ Ind i ^ ι ⁰) args args')
                       → sizeConv↑TermAll (All₂-stab Γ≡Δ ps) PE.≡ sizeConv↑TermAll ps
    stabilityAll₂Size Γ≡Δ []ₐ = PE.refl
    stabilityAll₂Size Γ≡Δ (p ∷ₐ ps) =
      PE.cong₂ _+_ (stabilitySizeConv↑Term Γ≡Δ p) (stabilityAll₂Size Γ≡Δ ps)

  stabilitySizeConv↓ : ∀ {k l Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↓] l ^ lA)
              → sizeConv↓ (stabilityConv↓ Γ≡Δ t~u) PE.≡
                sizeConv↓ t~u
  stabilitySizeConv↓ Γ≡Δ (U-refl x x₁) = PE.refl
  stabilitySizeConv↓ Γ≡Δ (univ x) = PE.cong 1+ (stabilitySizeConv↓Term Γ≡Δ x)

  stabilitySizeConv↑Term : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↑] l ∷ A ^ lA)
              → sizeConv↑Term (stabilityConv↑Term Γ≡Δ t~u) PE.≡
                sizeConv↑Term t~u
  stabilitySizeConv↑Term Γ≡Δ t~u = PE.cong 1+ (stabilitySizeConv↓Term Γ≡Δ (_⊢_[conv↑]_∷_^_.t<>u t~u))  

  stabilitySizeConv↑ : ∀ {k l Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↑] l ^ lA)
              → sizeConv↑ (stabilityConv↑ Γ≡Δ t~u) PE.≡
                sizeConv↑ t~u
  stabilitySizeConv↑ Γ≡Δ t~u = PE.cong 1+ (stabilitySizeConv↓ Γ≡Δ (_⊢_[conv↑]_^_.A′<>B′ t~u))  
