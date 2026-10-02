{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.DecView (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs as T
open import Definition.Typed.Properties senv swf equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Whnf senv swf equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Symmetry senv swf equivs
open import Definition.Conversion.SymmetrySize senv swf equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.StabilityProp senv swf equivs
open import Definition.Conversion.Conversion senv swf equivs
open import Definition.Conversion.ConversionProp senv swf equivs
open import Definition.Conversion.ConvSize senv equivs
open import Definition.Conversion.Lift senv swf equivs
open import Definition.Conversion.EqRelInstance senv swf equivs
open import Definition.Conversion.Inversion senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.Reduction senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Definition.Typed.Consequences.Inequality senv swf equivs as IE
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Definition.Typed.Consequences.TypeUnicity senv swf equivs
open import Definition.Conversion.HelperDecidable senv swf equivs
open import Definition.Conversion.DecidableLemmas senv swf equivs
open import Definition.Conversion.Consequences.Completeness senv swf equivs
open import Definition.Conversion.TransitivityHelper
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE
removeSuc : Nat → Nat
removeSuc 0 = 0
removeSuc (1+ n) = n

data Bool : Set where
  true : Bool
  false : Bool

is-diag~↑! : ∀ {k k' l l' R T Γ Δ lR lT}
         → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
         → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
         → Bool
is-diag~↑! e (cast-refl' _ _ _) = true
is-diag~↑! e (cast-refl _ _ _) = true
is-diag~↑! e (cast-cong _ _ _ _ _) = true
is-diag~↑! (cast-refl _ _ _) e = true
is-diag~↑! (cast-refl' _ _ _) e = true
is-diag~↑! (cast-cong _ _ _ _ _) e = true

is-diag~↑! (var-refl x x₁) (var-refl y y₁) = true
is-diag~↑! (var-refl x x₁) e' = false
is-diag~↑! (app-cong x x₁) (app-cong _ _) = true
is-diag~↑! (app-cong x x₁) e' = false
is-diag~↑! (Emptyrec-cong x x₁) (Emptyrec-cong _ _) = true
is-diag~↑! (Emptyrec-cong x x₁) e' = false
is-diag~↑! (cast-neΠ x x₁ x₂ x₃ x₄) (cast-neΠ _ _ _ _ _) = true
is-diag~↑! (cast-neΠ x x₁ x₂ x₃ x₄) e' = false
is-diag~↑! (cast-Π x x₁ x₂ x₃ x₄) (cast-Π _ _ _ _ _) = true
is-diag~↑! (cast-Π x x₁ x₂ x₃ x₄) e' = false
is-diag~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ%! _ _ _ _ _) = true
is-diag~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) e' = false
is-diag~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ!% _ _ _ _ _) = true
is-diag~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) e' = false
is-diag~↑! (IndRect-cong x x₁ x₂ x₃) (IndRect-cong _ _ _ _) = true
is-diag~↑! (IndRect-cong x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-neInd x x₁ x₂ x₃) (cast-neInd _ _ _ _) = true
is-diag~↑! (cast-neInd x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-Ind x x₁ x₂ x₃) (cast-Ind _ _ _ _) = true
is-diag~↑! (cast-Ind x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-IndΠ x x₁ x₂ x₃) (cast-IndΠ _ _ _ _) = true
is-diag~↑! (cast-IndΠ x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-ΠInd x x₁ x₂ x₃) (cast-ΠInd _ _ _ _) = true
is-diag~↑! (cast-ΠInd x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-IndInd x x₁ x₂ x₃) (cast-IndInd _ _ _ _) = true
is-diag~↑! (cast-IndInd x x₁ x₂ x₃) e' = false




¬~cast : ∀ {Γ k X Y e u}
       → (noeqcast : ∀ {A' B' t' e'} → k PE.≡ cast ⁰ A' B' e' t' → ⊥)
       → (noNeXY : Neutral X → Neutral Y → ⊥)
       → ¬ (∃ λ A → ∃ λ lA → Γ ⊢ k ~ cast ⁰ X Y e u ↑! A ^ lA)
¬~cast noeqcast noNeXY (_ , _ , cast-cong x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-refl x x₁ x₂) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-refl' x x₁ x₂) = let _ , neY , neX = ne~↓! x in noNeXY neX neY
¬~cast noeqcast noNeXY (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-Π x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-neInd x x₁ x₂ x₃) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-Ind x x₁ x₂ x₃) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-IndΠ x x₁ x₂ x₃) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-ΠInd x x₁ x₂ x₃) = noeqcast PE.refl
¬~cast noeqcast noNeXY (_ , _ , cast-IndInd x x₁ x₂ x₃) = noeqcast PE.refl

¬cast~ : ∀ {Γ l X Y e t}
       → (noeqcast : ∀ {A' B' t' e'} → l PE.≡ cast ⁰ A' B' e' t' → ⊥)
       → (noNeXY : Neutral X → Neutral Y → ⊥)
       → ¬ (∃ λ A → ∃ λ lA → Γ ⊢ cast ⁰ X Y e t ~ l ↑! A ^ lA)
¬cast~ noeqcast noNeXY (_ , _ , cast-cong x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-refl x x₁ x₂) = let _ , neX , neY = ne~↓! x in noNeXY neX neY
¬cast~ noeqcast noNeXY (_ , _ , cast-refl' x x₁ x₂) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-Π x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-neInd x x₁ x₂ x₃) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-Ind x x₁ x₂ x₃) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-IndΠ x x₁ x₂ x₃) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-ΠInd x x₁ x₂ x₃) = noeqcast PE.refl
¬cast~ noeqcast noNeXY (_ , _ , cast-IndInd x x₁ x₂ x₃) = noeqcast PE.refl

¬cast~cast : ∀ {Γ X Y e t X' Y' e' t'}
           → (noNeXY : Neutral X → Neutral Y → ⊥)
           → (noNeXY' : Neutral X' → Neutral Y' → ⊥)
           → (noNeNe : Neutral X → Neutral X' → ⊥)
           → (noΠ : ∀ {A rA P A' P'} → X PE.≡ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! → X' PE.≡ Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! → ⊥)
           → (noInd : ∀ {i} → X PE.≡ Ind i → X' PE.≡ Ind i → ⊥)
           → ¬ (∃ λ A → ∃ λ lA → Γ ⊢ cast ⁰ X Y e t ~ cast ⁰ X' Y' e' t' ↑! A ^ lA)
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-cong x x₁ x₂ x₃ x₄) = let _ , neX , neX' = ne~↓! x in noNeNe neX neX'
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-refl x x₁ x₂) = let _ , neX , neY = ne~↓! x in noNeXY neX neY
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-refl' x x₁ x₂) = let _ , neY' , neX' = ne~↓! x in noNeXY' neX' neY'
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) = let _ , neX , neX' = ne~↓! x₁ in noNeNe neX neX'
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-Π x x₁ x₂ x₃ x₄) = noΠ PE.refl PE.refl
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) = noΠ PE.refl PE.refl
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) = noΠ PE.refl PE.refl
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-neInd x x₁ x₂ x₃) = let _ , neX , neX' = ne~↓! x in noNeNe neX neX'
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-Ind x x₁ x₂ x₃) = noInd PE.refl PE.refl
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-IndΠ x x₁ x₂ x₃) = noInd PE.refl PE.refl
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-ΠInd x x₁ x₂ x₃) = noΠ PE.refl PE.refl
¬cast~cast noNeXY noNeXY' noNeNe noΠ noInd (_ , _ , cast-IndInd x x₁ x₂ x₃) = noInd PE.refl PE.refl
¬head~head : ∀ {Γ k l}
           → (noeqcast : ∀ {A' B' t' e'} → k PE.≡ cast ⁰ A' B' e' t' → ⊥)
           → (noeqcast' : ∀ {A' B' t' e'} → l PE.≡ cast ⁰ A' B' e' t' → ⊥)
           → (novar : ∀ {x y} → k PE.≡ var x → l PE.≡ var y → ⊥)
           → (nogen : ∀ {K c c'} → k PE.≡ gen K c → l PE.≡ gen K c' → ⊥)
           → ¬ (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↑! A ^ lA)
¬head~head noeqcast noeqcast' novar nogen (_ , _ , var-refl x x₁) = novar PE.refl PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , app-cong x x₁) = nogen PE.refl PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , IndRect-cong x x₁ x₂ x₃) = nogen PE.refl PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , Emptyrec-cong x x₁) = nogen PE.refl PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-cong x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-refl x x₁ x₂) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-refl' x x₁ x₂) = noeqcast' PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-Π x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-neInd x x₁ x₂ x₃) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-Ind x x₁ x₂ x₃) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-IndΠ x x₁ x₂ x₃) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-ΠInd x x₁ x₂ x₃) = noeqcast PE.refl
¬head~head noeqcast noeqcast' novar nogen (_ , _ , cast-IndInd x x₁ x₂ x₃) = noeqcast PE.refl

abstract
  not-diag~↑! : ∀ {k k' l l' R T Γ Δ lR lT}
           → ⊢ Γ ≡ Δ
           → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
           → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
           → is-diag~↑! e e' PE.≡ false
           → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↑! A ^ lA)
  not-diag~↑! Γ≡Δ (var-refl x x₁) (app-cong y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ {_ ()}) (λ ()))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (Emptyrec-cong y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ {_ ()}) (λ ()))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-neΠ y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-Π y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (IndRect-cong y y₁ y₂ y₃) _ = no (¬head~head (λ ()) (λ ()) (λ {_ ()}) (λ ()))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-neInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-Ind y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-IndΠ y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-ΠInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-IndInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))

  not-diag~↑! Γ≡Δ (app-cong x x₁) (var-refl y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ {_ ()}))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (Emptyrec-cong y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ { PE.refl () }))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-Π y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-neΠ y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (IndRect-cong y y₁ y₂ y₃) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ { PE.refl () }))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-neInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-Ind y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-IndΠ y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-ΠInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (app-cong x x₁) (cast-IndInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))


  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ {_ ()}))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ { PE.refl () }))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-Π y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-neΠ y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (IndRect-cong y y₁ y₂ y₃) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ { PE.refl () }))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-neInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-Ind y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-IndΠ y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ΠInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-IndInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))



  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (var-refl x₄ x₅) _ = castneΠ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()})
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (app-cong x₄ x₅) _ = castneΠ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()})
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = castneΠ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()})

  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
      castneΠ-refl'-dec~ x
                    (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                   in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                    (λ neA e → let _ , eA , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eA) neA) )
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
      castneΠ-refl'-dec~ x
                    (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                   in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                    (λ neA e → let _ , eA , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eA) neA) )
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ =  no (λ (_ , _ , X) → let _ , _ , neA = ne~↓! x₅ in IE.Π≢ne neA (cast-cast-≡ X))


  not-diag~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) (cast-neInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) (cast-Ind y y₁ y₂ y₃) _ =
    let _ , _ , nY' = ne~↓! y
    in no (λ (_ , _ , X) → IE.Π≢ne nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) (cast-IndΠ y y₁ y₂ y₃) _ =
    let _ , nX , _ = ne~↓! x₁
    in no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ _ n → noNeInd n) (λ {_ ()}) (λ e _ → noNeInd (PE.subst Neutral e nX)))
  not-diag~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) (cast-ΠInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) (cast-IndInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))

  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-neΠ y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY = ne~↓! x₁
    in no (λ (_ , _ , X) → IE.Π≢ne nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-neInd y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x₁
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-Ind y y₁ y₂ y₃) _ =
    no (¬cast~cast (λ n _ → noNeΠ n) (λ n _ → noNeInd n)
                    (λ n _ → noNeΠ n) (λ {_ ()}) (λ ()))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-IndΠ y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x₁
    in no (λ (_ , _ , X) → IE.Π≢ne nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ΠInd y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x₁
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-IndInd y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x₁
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY (sym (cast-cast-≡ X)))




  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ =
    no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeΠ n) (λ { PE.refl () }) (λ ()))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-neΠ y y₁ y₂ y₃ y₄) _ =
    let _ , nX' , _ = ne~↓! y₁
    in no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeΠ n) (λ _ e → noNeΠ (PE.subst Neutral e nX')) (λ ()))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-neInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Ind y y₁ y₂ y₃) _ =
    let _ , _ , nY' = ne~↓! y
    in no (λ (_ , _ , X) → IE.Π≢ne nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-IndΠ y y₁ y₂ y₃) _ =
    no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeΠ n) (λ {_ ()}) (λ ()))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-IndInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))

  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ =
    no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeΠ n) (λ { PE.refl () }) (λ ()))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-neΠ y y₁ y₂ y₃ y₄) _ =
    let _ , nX' , _ = ne~↓! y₁
    in no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeΠ n) (λ _ e → noNeΠ (PE.subst Neutral e nX')) (λ ()))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-neInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Ind y y₁ y₂ y₃) _ =
    let _ , _ , nY' = ne~↓! y
    in no (λ (_ , _ , X) → IE.Π≢ne nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-IndΠ y y₁ y₂ y₃) _ =
    no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeΠ n) (λ {_ ()}) (λ ()))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-IndInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))

  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (var-refl y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ {_ ()}))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (app-cong y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ { PE.refl () }))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (Emptyrec-cong y y₁) _ = no (¬head~head (λ ()) (λ ()) (λ ()) (λ { PE.refl () }))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-neΠ y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-Π y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ n _ → noNeΠ n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-neInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-Ind y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-IndΠ y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-ΠInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (IndRect-cong x x₁ x₂ x₃) (cast-IndInd y y₁ y₂ y₃) _ = no (¬~cast (λ ()) (λ _ n → noNeInd n))

  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-neΠ y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-Π y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY' = ne~↓! y₁
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-Ind y y₁ y₂ y₃) _ =
    let _ , _ , nY' = ne~↓! y
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-IndΠ y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-ΠInd y y₁ y₂ y₃) _ =
    let _ , nX , _ = ne~↓! x
    in no (¬cast~cast (λ _ n → noNeInd n) (λ _ n → noNeInd n)
                    (λ _ n → noNeΠ n) (λ e _ → noNeΠ (PE.subst Neutral e nX)) (λ {_ ()}))
  not-diag~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) (cast-IndInd y y₁ y₂ y₃) _ =
    let _ , nX , _ = ne~↓! x
    in no (¬cast~cast (λ _ n → noNeInd n) (λ _ n → noNeInd n)
                    (λ _ n → noNeInd n) (λ {_ ()}) (λ e _ → noNeInd (PE.subst Neutral e nX)))

  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-neΠ y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY = ne~↓! x
    in no (λ (_ , _ , X) → IE.Π≢ne nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-Π y y₁ y₂ y₃ y₄) _ =
    no (¬cast~cast (λ n _ → noNeInd n) (λ n _ → noNeΠ n)
                    (λ n _ → noNeInd n) (λ ()) (λ {_ ()}))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY = ne~↓! x
    in no (λ (_ , _ , X) → IE.Π≢ne nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY = ne~↓! x
    in no (λ (_ , _ , X) → IE.Π≢ne nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ n _ → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-neInd y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-IndΠ y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x
    in no (λ (_ , _ , X) → IE.Π≢ne nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-ΠInd y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Ind x x₁ x₂ x₃) (cast-IndInd y y₁ y₂ y₃) _ =
    let _ , _ , nY = ne~↓! x
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY (sym (cast-cast-≡ X)))

  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-neΠ y y₁ y₂ y₃ y₄) _ =
    let _ , nX' , _ = ne~↓! y₁
    in no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeInd n) (λ ()) (λ _ e → noNeInd (PE.subst Neutral e nX')))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-Π y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY' = ne~↓! y₁
    in no (λ (_ , _ , X) → IE.Π≢ne nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ =
    no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeInd n) (λ ()) (λ {_ ()}))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ =
    no (¬cast~cast (λ _ n → noNeΠ n) (λ _ n → noNeΠ n)
                    (λ n _ → noNeInd n) (λ ()) (λ {_ ()}))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ _ n → noNeΠ n))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-neInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-Ind y y₁ y₂ y₃) _ =
    let _ , _ , nY' = ne~↓! y
    in no (λ (_ , _ , X) → IE.Π≢ne nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-ΠInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-IndInd y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Π≢Ind! (cast-cast-≡ X))

  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-neΠ y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-Π y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY' = ne~↓! y₁
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-neInd y y₁ y₂ y₃) _ =
    let _ , nX' , _ = ne~↓! y
    in no (¬cast~cast (λ _ n → noNeInd n) (λ _ n → noNeInd n)
                    (λ n _ → noNeΠ n) (λ _ e → noNeΠ (PE.subst Neutral e nX')) (λ ()))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-Ind y y₁ y₂ y₃) _ =
    let _ , _ , nY' = ne~↓! y
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-IndΠ y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-IndInd y y₁ y₂ y₃) _ =
    no (¬cast~cast (λ _ n → noNeInd n) (λ _ n → noNeInd n)
                    (λ n _ → noNeΠ n) (λ {_ ()}) (λ ()))



  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (var-refl y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (app-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (Emptyrec-cong y y₁) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-neΠ y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-Π y y₁ y₂ y₃ y₄) _ =
    let _ , _ , nY' = ne~↓! y₁
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-ΠΠ%! y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-ΠΠ!% y y₁ y₂ y₃ y₄) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (IndRect-cong y y₁ y₂ y₃) _ = no (¬cast~ (λ ()) (λ _ n → noNeInd n))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-neInd y y₁ y₂ y₃) _ =
    let _ , nX' , _ = ne~↓! y
    in no (¬cast~cast (λ _ n → noNeInd n) (λ _ n → noNeInd n)
                    (λ n _ → noNeInd n) (λ ()) (λ _ e → noNeInd (PE.subst Neutral e nX')))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-Ind y y₁ y₂ y₃) _ =
    let _ , _ , nY' = ne~↓! y
    in no (λ (_ , _ , X) → IE.Ind≢ne! nY' (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-IndΠ y y₁ y₂ y₃) _ = no (λ (_ , _ , X) → IE.Ind≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) (cast-ΠInd y y₁ y₂ y₃) _ =
    no (¬cast~cast (λ _ n → noNeInd n) (λ _ n → noNeInd n)
                    (λ n _ → noNeInd n) (λ ()) (λ {_ ()}))

  not-diag~↑! Γ≡Δ e (cast-cong _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ e (cast-refl _ _ _) ()
  not-diag~↑! Γ≡Δ e (cast-refl' _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (var-refl _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (app-cong _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (Emptyrec-cong _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-neΠ _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-Π _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-ΠΠ%! _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-ΠΠ!% _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (IndRect-cong _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-neInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-Ind _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-IndΠ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-ΠInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-cong _ _ _ _ _) (cast-IndInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (var-refl _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (app-cong _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (Emptyrec-cong _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-neΠ _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-Π _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-ΠΠ%! _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-ΠΠ!% _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (IndRect-cong _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-neInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-Ind _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-IndΠ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-ΠInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl _ _ _) (cast-IndInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (var-refl _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (app-cong _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (Emptyrec-cong _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-neΠ _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-Π _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-ΠΠ%! _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-ΠΠ!% _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (IndRect-cong _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-neInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-Ind _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-IndΠ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-ΠInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-refl' _ _ _) (cast-IndInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (var-refl _ _) (var-refl _ _) ()
  not-diag~↑! Γ≡Δ (app-cong _ _) (app-cong _ _) ()
  not-diag~↑! Γ≡Δ (Emptyrec-cong _ _) (Emptyrec-cong _ _) ()
  not-diag~↑! Γ≡Δ (cast-neΠ _ _ _ _ _) (cast-neΠ _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-Π _ _ _ _ _) (cast-Π _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! _ _ _ _ _) (cast-ΠΠ%! _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% _ _ _ _ _) (cast-ΠΠ!% _ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (IndRect-cong _ _ _ _) (IndRect-cong _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-neInd _ _ _ _) (cast-neInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-Ind _ _ _ _) (cast-Ind _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-IndΠ _ _ _ _) (cast-IndΠ _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-ΠInd _ _ _ _) (cast-ΠInd _ _ _ _) ()
  not-diag~↑! Γ≡Δ (cast-IndInd _ _ _ _) (cast-IndInd _ _ _ _) ()

-- data view~↑! : ∀ {k k' l l' R T Γ Δ lR lT}
--         → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
--         → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
--         → Set
--   where
--     x-castrefl' : ∀ {Γ k k' R lR Δ A B t u e}
--       (k~k' : Γ ⊢ k ~ k' ↑! R ^ lR)
--       (A~A : Δ ⊢ B ~ A ↓! U ⁰ ^ next ⁰)
--       (t≡u : Δ ⊢ t [conv↓] u ∷ A ^ ι ⁰)
--       (⊢e' : Δ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
--       → view~↑! k~k' (cast-refl' A~A t≡u ⊢e')
--     castrefl'-x : ∀ {Γ A B t u e Δ l l' T lT}
--       (A~A : Γ ⊢ B ~ A ↓! U ⁰ ^ next ⁰)
--       (t≡u : Γ ⊢ t [conv↓] u ∷ A ^ ι ⁰)
--       (⊢e' : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
--       (l~l' : Δ ⊢ l ~ l' ↑! T ^ lT)
--       → view~↑! (cast-refl' A~A t≡u ⊢e') l~l'
--     x-castℕrefl' : ∀ {Γ k k' R lR Δ t u e}
--       (k~k' : Γ ⊢ k ~ k' ↑! R ^ lR)
--       (t~u : Δ ⊢ t ~ u ↓! ℕ ^ ι ⁰)
--       (⊢e : Δ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
--       → view~↑! k~k' (castℕ-refl' t~u ⊢e)
--     castℕrefl'-x : ∀ {Γ t u e Δ l l' T lT}
--       (t~u : Γ ⊢ t ~ u ↓! ℕ ^ ι ⁰)
--       (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
--       (l~l' : Δ ⊢ l ~ l' ↑! T ^ lT)
--       → view~↑! (castℕ-refl' t~u ⊢e) l~l'
--     varrefl-diag : ∀ {Γ n n' A l Δ m m' B l'}
--       (⊢x : Γ ⊢ var n ∷ A ^ [ ! , l ])
--       (n≡n : n PE.≡ n')
--       (⊢y : Δ ⊢ var m ∷ B ^ [ ! , l' ])
--       (m≡m : m PE.≡ m')
--       → view~↑! (var-refl ⊢x n≡n) (var-refl ⊢y m≡m)
--     appcong-diag : ∀ {Γ k l t v F rF lF lG G lΠ Δ k' l' t' v' F' rF' lF' lG' G' lΠ'}
--       (x~x : Γ ⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ)
--       (t≡t : Γ ⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ])
--       (y~y : Δ ⊢ k' ~ l' ↓! Π F' ^ rF' ° lF' ▹ G' ° lG' ° lΠ' ^ ! ^ ι lΠ')
--       (u≡u : Δ ⊢ t' [genconv↑] v' ∷ F' ^ [ rF' , ι lF' ])
--       → view~↑! (app-cong x~x t≡t) (app-cong y~y u≡u)
