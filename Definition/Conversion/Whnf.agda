{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.Whnf (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Conversion senv equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Tools.Product
mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑! : ∀ {t u A Γ l}
       → Γ ⊢ t ~ u ↑! A ^ l
       → Neutral t × Neutral u
  ne~↑! (var-refl x₁ x≡y) = var _ , var _
  ne~↑! (app-cong x x₁) = let _ , q , w = ne~↓! x
                         in  ∘ₙ q , ∘ₙ w
  ne~↑! (Emptyrec-cong x x₁) = Emptyrecₙ , Emptyrecₙ
  ne~↑! (cast-cong X x x₁ x₂ x₃) =
    let _ , nX , nX' = ne~↓! X
        _ , nx' , nx = ne~↓! x
        nt , nt' = whnfConv↓TermNe nX x₁
    in castₙ nX nx nt , castₙ nX' nx' nt'
  ne~↑! (cast-Π x X x₁ x₂ x₃) = let _ , nt , nu = ne~↓! X in castΠₙ nu , castΠₙ nt
  ne~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = castΠΠ%!ₙ , castΠΠ%!ₙ
  ne~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = castΠΠ!%ₙ , castΠΠ!%ₙ
  ne~↑! (cast-refl x x₁ x₂) =
    let _ , nA , nB = ne~↓! x
        nt , nt' = whnfConv↓TermNe nA x₁
     in castₙ nA nB nt , nt'
  ne~↑! (cast-refl' x x₁ x₂) =
    let _ , nB , nA = ne~↓! x
        nt , nt' = whnfConv↓TermNe nA x₁
    in nt , castₙ nA nB nt'
  ne~↑! (cast-neΠ x x₁ x₂ x₃ x₄) = let _ , nA , nB = ne~↓! x₁ in castnΠₙ nA , castnΠₙ nB
  ne~↑! (IndRect-cong _ x x₁ x₂) = let _ , nt , nu = ne~↓! x₁ in IndRectₙ nt , IndRectₙ nu
  ne~↑! (cast-neInd x x₁ x₂ x₃) = let _ , nA , nB = ne~↓! x in castnIndₙ nA , castnIndₙ nB
  ne~↑! (cast-Ind x x₁ x₂ x₃) = let _ , nA' , nA = ne~↓! x in castIndₙ nA , castIndₙ nA'
  ne~↑! (cast-IndΠ x x₁ x₂ x₃) = castIndΠₙ , castIndΠₙ
  ne~↑! (cast-ΠInd x x₁ x₂ x₃) = castΠIndₙ , castΠIndₙ
  ne~↑! (cast-IndInd x x₁ x₂ x₃) = castIndInd≢ₙ x , castIndInd≢ₙ x

  ne~↓! : ∀ {t u A Γ l}
        → Γ ⊢ t ~ u ↓! A ^ l
        → Whnf A × Neutral t × Neutral u
  ne~↓! ([~] A D whnfB k~l) = whnfB , ne~↑! k~l

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
  whnfConv↓Term : ∀ {t u A Γ l}
                → Γ ⊢ t [conv↓] u ∷ A ^ l
                → Whnf A × Whnf t × Whnf u
  whnfConv↓Term (Ind-ins x) = let _ , neT , neU = ne~↓! x
                             in Indₙ , ne neT , ne neU
  whnfConv↓Term (ne x) = let wA , nt , nu = ne~↓! x in wA , ne nt , ne nu
  whnfConv↓Term (ne-ins t u x x₁) =
    let _ , neT , neU = ne~↓! x₁
    in ne x , ne neT , ne neU
  whnfConv↓Term (Empty-refl x) = Uₙ , Emptyₙ , Emptyₙ
  whnfConv↓Term (Π-cong _ _ _ _ _ _ x x₁ x₂) = Uₙ , Πₙ , Πₙ
  whnfConv↓Term (Id-cong x x₁ x₂) = Uₙ , Idₙ , Idₙ
  whnfConv↓Term (U-refl _ _) = Uₙ , Uₙ , Uₙ
  whnfConv↓Term (η-eq _ _ x x₁ x₂ y y₁ x₃) = Πₙ , functionWhnf y , functionWhnf y₁
  whnfConv↓Term (Ind-refl x _) = Uₙ , Indₙ , Indₙ
  whnfConv↓Term (ctr-cong _ _ _ x) = Indₙ , ctrₙ , ctrₙ
  
  -- Extraction of WHNF from algorithmic equality of types in WHNF.
  whnfConv↓ : ∀ {A B rA Γ}
            → Γ ⊢ A [conv↓] B ^ rA
            → Whnf A × Whnf B
  whnfConv↓ (U-refl _ _) = Uₙ , Uₙ
  whnfConv↓ (univ x₂) = let _ , A , B = whnfConv↓Term x₂ in A , B
  
-- Extraction of Neutrals from algorithmic equality of terms in WHNF, when the type is neutral.
  whnfConv↓TermNe : ∀ {t u A Γ l}
                → Neutral A
                → Γ ⊢ t [conv↓] u ∷ A ^ l
                → Neutral t × Neutral u
  whnfConv↓TermNe neA (ne-ins x x₁ x₂ x₃) =
    let _ , neT , neU = ne~↓! x₃
    in neT , neU
