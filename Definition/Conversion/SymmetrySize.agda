import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.SymmetrySize (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Conversion senv swf equivs
open import Definition.Conversion.Whnf senv swf equivs
open import Definition.Conversion.ConvSize senv equivs
open import Definition.Conversion.ConversionProp senv swf equivs
open import Definition.Conversion.Symmetry senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Definition.Typed.Consequences.Reduction senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Definition.Typed.Consequences.SucCong senv swf equivs
open import Tools.Product
open import Tools.List using (All₂; []ₐ; _∷ₐ_)
import Tools.PropositionalEquality as PE
open import Tools.Nat
size-subst : ∀ {t u A B Γ r} (A≡B : A PE.≡ B) (t~u : Γ ⊢ t ~ u ↓! A ^ r)
           → size~↓! (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) A≡B t~u) PE.≡ size~↓! t~u
size-subst PE.refl t~u = PE.refl

mutual
  -- Symmetry of algorithmic equality of neutrals
  size-sym~↑! : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t ~ u ↑! A ^ l) → size~↑! (proj₂ (proj₂ (sym~↑! Γ≡Δ t~u))) PE.≡ size~↑! t~u
  size-sym~↑! Γ≡Δ (var-refl x x₁) = PE.refl
  size-sym~↑! Γ≡Δ (app-cong {rF = !} t~u x₁) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        F′ , G′ , ΠF′G′≡B = Π≡A A≡B whnfB
        F≡F′ , rF≡rF′ , lF≡lF' , lG≡lG' , G≡G′ = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) ΠF′G′≡B A≡B)
        ex = size-sym~↓! Γ≡Δ t~u
        ex' = size-symConv↑Term Γ≡Δ x₁
        a = PE.trans (size-subst ΠF′G′≡B u~t) ex
        b = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) ex'
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (app-cong {rF = %} t~u x₁) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        F′ , G′ , ΠF′G′≡B = Π≡A A≡B whnfB
        F≡F′ , rF≡rF′ , lF≡lF' , lG≡lG' , G≡G′ = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) ΠF′G′≡B A≡B)
        ex = size-sym~↓! Γ≡Δ t~u
        a = PE.trans (size-subst ΠF′G′≡B u~t) ex
    in PE.cong₂ (λ X Y → 1 + X + Y) a PE.refl
  size-sym~↑! Γ≡Δ (natrec-cong x x₁ x₂ t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
        F≡G = stabilityEq (Γ≡Δ ∙ refl (univ (ℕⱼ ⊢Γ))) (soundnessConv↑ x)
        F[0]≡G[0] = substTypeEq F≡G (refl (zeroⱼ ⊢Δ))
        a : sizeConv↑ (symConv↑ (Γ≡Δ ∙ (refl (univ (ℕⱼ ⊢Γ)))) x) PE.≡ sizeConv↑ x
        a = size-symConv↑ (Γ≡Δ ∙ (refl (univ (ℕⱼ ⊢Γ)))) x
        b : sizeConv↑Term (convConvTerm (symConv↑Term Γ≡Δ x₁) F[0]≡G[0]) PE.≡ sizeConv↑Term x₁
        b = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
        c = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₂)) (size-symConv↑Term Γ≡Δ x₂)
        d = PE.trans (size-subst B≡ℕ u~t) (size-sym~↓! Γ≡Δ t~u)
    in PE.cong₄ (λ X Y Z T → 1 + X + Y + Z + T) a b c d
  size-sym~↑! Γ≡Δ (Emptyrec-cong x t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        u~t = sym~↑% Γ≡Δ t~u
        a = size-symConv↑ Γ≡Δ x
    in PE.cong (λ X → 1 + X) a
  size-sym~↑! Γ≡Δ (cast-cong X x x₁ x₂ x₃) =
    let U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ X
        UB , whnfUB , U≡UB' , B'~B = sym~↓! Γ≡Δ x
        U≡B = U≡A-whnf U≡U' whnfU
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
        U≡B' = U≡A-whnf U≡UB' whnfUB
        B'≡B = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B' B'~B
        t'~t = symConv↓Term Γ≡Δ x₁
        _ , neA , neA' = ne~↓! X
        ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        a = PE.trans (size-subst U≡B A'~A) (size-sym~↓! Γ≡Δ X)
        b = PE.trans (size-subst U≡B' B'~B) (size-sym~↓! Γ≡Δ x)
        c = PE.trans (convConv↓TermSize _ _ _ t'~t) (size-symConv↓Term Γ≡Δ x₁)
    in PE.cong₃ (λ X Y Z → 1 + X + Y + Z) a b c
  size-sym~↑! Γ≡Δ (cast-refl x x₁ x₂) =
    let A≡A = soundness~↓! x
        _ , neA , neA' = ne~↓! x
        ⊢A , ⊢A' = syntacticEq (univ A≡A)
        t'~t = symConv↓Term Γ≡Δ x₁
        ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        U , whnfU , U≡U , A~B = sym~↓! Γ≡Δ x
        U≡B = U≡A-whnf U≡U whnfU
        A≡B = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A~B
        a = PE.trans (size-subst U≡B A~B) (size-sym~↓! Γ≡Δ x)
        b = PE.trans (convConv↓TermSize _ _ _ t'~t) (size-symConv↓Term Γ≡Δ x₁)
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (castℕ-refl x x₁) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , N≡B , u~t = sym~↓! Γ≡Δ x
        B≡ℕ = ℕ≡A N≡B whnfB
        a = PE.trans (size-subst B≡ℕ u~t) (size-sym~↓! Γ≡Δ x)
    in PE.cong (λ X → 1 + X) a
  size-sym~↑! Γ≡Δ (castInd-refl x x₁) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , N≡B , u~t = sym~↓! Γ≡Δ x
        B≡Ind = Ind≡A N≡B whnfB
        a = PE.trans (size-subst B≡Ind u~t) (size-sym~↓! Γ≡Δ x)
    in PE.cong (λ X → 1 + X) a
  size-sym~↑! Γ≡Δ (castInd-refl' x x₁) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , N≡B , u~t = sym~↓! Γ≡Δ x
        B≡Ind = Ind≡A N≡B whnfB
        a = PE.trans (size-subst B≡Ind u~t) (size-sym~↓! Γ≡Δ x)
    in PE.cong (λ X → 1 + X) a
  size-sym~↑! Γ≡Δ (cast-refl' x x₁ x₂) =
    let A≡A = soundness~↓! x
        _ , neA' , neA = ne~↓! x
        ⊢A' , ⊢A = syntacticEq (univ A≡A)
        t'~t = symConv↓Term Γ≡Δ x₁
        ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        U , whnfU , U≡U , A~B = sym~↓! Γ≡Δ x
        U≡B = U≡A-whnf U≡U whnfU
        A≡B = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A~B
        a = PE.trans (size-subst U≡B A~B) (size-sym~↓! Γ≡Δ x)
        b = PE.trans (convConv↓TermSize _ _ _ t'~t) (size-symConv↓Term Γ≡Δ x₁)
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (castℕ-refl' x x₁) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , N≡B , u~t = sym~↓! Γ≡Δ x
        B≡ℕ = ℕ≡A N≡B whnfB
        a = PE.trans (size-subst B≡ℕ u~t) (size-sym~↓! Γ≡Δ x)
    in PE.cong (λ X → 1 + X) a
  size-sym~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ x
        U≡B = U≡A-whnf U≡U' whnfU
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
        a = PE.trans (size-subst U≡B A'~A) (size-sym~↓! Γ≡Δ x)
        b = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (cast-neInd x x₁ x₂ x₃) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ x
        U≡B = U≡A-whnf U≡U' whnfU
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
        a = PE.trans (size-subst U≡B A'~A) (size-sym~↓! Γ≡Δ x)
        b = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (cast-Ind X x x₁ x₂) =
    let U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ X
        B'~B = symConv↑Term Γ≡Δ x
        U≡B = U≡A-whnf U≡U' whnfU
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
        a = PE.trans (size-subst U≡B A'~A) (size-sym~↓! Γ≡Δ X)
        b = size-symConv↑Term Γ≡Δ x
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (cast-ℕ X x x₁ x₂) =
    let U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ X
        B'~B = symConv↑Term Γ≡Δ x
        U≡B = U≡A-whnf U≡U' whnfU
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
        a = PE.trans (size-subst U≡B A'~A) (size-sym~↓! Γ≡Δ X)
        b = size-symConv↑Term Γ≡Δ x
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ x
        U≡B = U≡A-whnf U≡U' whnfU
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
        a = size-symConv↑Term Γ≡Δ X
        b = PE.trans (size-subst U≡B A'~A) (size-sym~↓! Γ≡Δ x)
        c = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
    in PE.cong₃ (λ X Y Z → 1 + X + Y + Z) a b c
  size-sym~↑! Γ≡Δ (cast-Π x X x₁ x₂ x₃) =
    let U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ X
        B'~B = symConv↑Term Γ≡Δ x
        U≡B = U≡A-whnf U≡U' whnfU
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
        a = size-symConv↑Term Γ≡Δ x
        b = PE.trans (size-subst U≡B A'~A) (size-sym~↓! Γ≡Δ X)
        c = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
    in PE.cong₃ (λ X Y Z → 1 + X + Y + Z) a b c
  size-sym~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        a = size-symConv↑Term Γ≡Δ x
        b = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
    in PE.cong₂ (λ X Y → 1 + X + Y) a b
  size-sym~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) = PE.cong₂ (λ X Y → 1 + X + Y) (size-symConv↑Term Γ≡Δ x) (size-symConv↑Term Γ≡Δ x₁)
  size-sym~↑! Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) =
    PE.cong₂ (λ X Y → 1 + X + Y) (size-symConv↑Term Γ≡Δ x) (size-symConv↑Term Γ≡Δ x₁)
  size-sym~↑! Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) =
    let b = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
    in PE.cong₂ (λ X Y → 1 + X + Y) (size-symConv↑Term Γ≡Δ x) b
  size-sym~↑! Γ≡Δ (cast-Indℕ x x₁ x₂) = PE.cong (λ X → 1 + X) (size-symConv↑Term Γ≡Δ x)
  size-sym~↑! Γ≡Δ (cast-ℕInd x x₁ x₂) = PE.cong (λ X → 1 + X) (size-symConv↑Term Γ≡Δ x)
  size-sym~↑! Γ≡Δ (cast-IndInd x x₁ x₂ x₃) = PE.cong (λ X → 1 + X) (size-symConv↑Term Γ≡Δ x₁)
  size-sym~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) =
    let a = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₂)) (size-symConv↑Term Γ≡Δ x₂)
    in PE.cong₃ (λ X Y Z → 1 + X + Y + Z) (size-symConv↑Term Γ≡Δ x) (size-symConv↑Term Γ≡Δ x₁) a
  size-sym~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) =
    let a = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₂)) (size-symConv↑Term Γ≡Δ x₂)
    in PE.cong₃ (λ X Y Z → 1 + X + Y + Z) (size-symConv↑Term Γ≡Δ x) (size-symConv↑Term Γ≡Δ x₁) a
  size-sym~↑! Γ≡Δ (IndRect-cong _ x x₁ x₂) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        B , whnfB , Ind≡B , t'~t = sym~↓! Γ≡Δ x₁
        B≡Ind = Ind≡A Ind≡B whnfB
        a = size-symConv↑ (Γ≡Δ ∙ (refl (univ (Indⱼ ⊢Γ)))) x
        b = PE.trans (size-subst B≡Ind t'~t) (size-sym~↓! Γ≡Δ x₁)
    in PE.cong₂ (λ X Y → 1 + X + Y) a b

  size-sym~↓! : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t ~ u ↓! A ^ l) → size~↓! (proj₂ (proj₂ (proj₂ (sym~↓! Γ≡Δ t~u)))) PE.≡ size~↓! t~u
  size-sym~↓! Γ≡Δ ([~] A D whnfB k~l) = PE.cong 1+ (size-sym~↑! Γ≡Δ k~l)

  size-symConv↑Term : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t [conv↑] u ∷ A ^ l) → sizeConv↑Term (symConv↑Term Γ≡Δ t~u) PE.≡ sizeConv↑Term t~u
  size-symConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = PE.cong (λ X → 1 + X) (size-symConv↓Term Γ≡Δ t<>u)

  size-symConv↑ : ∀ {A B Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (A~B : Γ ⊢ A [conv↑] B ^ l) → sizeConv↑ (symConv↑ Γ≡Δ A~B) PE.≡ sizeConv↑ A~B
  size-symConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) = PE.cong (λ X → 1 + X) (size-symConv↓ Γ≡Δ A′<>B′)

  size-symConv↓Term : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t [conv↓] u ∷ A ^ l) → sizeConv↓Term (symConv↓Term Γ≡Δ t~u) PE.≡ sizeConv↓Term t~u
  size-symConv↓Term Γ≡Δ (U-refl x x₁) = PE.refl
  size-symConv↓Term Γ≡Δ (ne t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        U≡B = U≡A-whnf A≡B whnfB
        a = PE.trans (size-subst U≡B u~t) (size-sym~↓! Γ≡Δ t~u)
    in PE.cong (λ X → 1 + X) a
  size-symConv↓Term Γ≡Δ (ℕ-refl x) = PE.refl
  size-symConv↓Term Γ≡Δ (Empty-refl x) = PE.refl
  size-symConv↓Term Γ≡Δ (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' x A<>B A<>B₁) =
    let F≡H = soundnessConv↑Term A<>B
        _ , ⊢H = syntacticEq (stabilityEq Γ≡Δ (univ F≡H))
    in PE.cong₂ (λ X Y → 1 + X + Y) (size-symConv↑Term Γ≡Δ A<>B) (size-symConv↑Term (Γ≡Δ ∙ univ F≡H) A<>B₁)
  size-symConv↓Term Γ≡Δ (Id-cong X x x₁) =
    let a = size-symConv↑Term Γ≡Δ X
        b = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x)) (size-symConv↑Term Γ≡Δ x)
        c = PE.trans (convConv↑TermSize _ _ (symConv↑Term Γ≡Δ x₁)) (size-symConv↑Term Γ≡Δ x₁)
    in PE.cong₃ (λ X Y Z → 1 + X + Y + Z) a b c
  size-symConv↓Term Γ≡Δ (ℕ-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
        a = PE.trans (size-subst B≡ℕ u~t) (size-sym~↓! Γ≡Δ t~u)
    in PE.cong (λ X → 1 + X) a
  size-symConv↓Term Γ≡Δ (Ind-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        B≡Ind = Ind≡A A≡B whnfB
        a = PE.trans (size-subst B≡Ind u~t) (size-sym~↓! Γ≡Δ t~u)
    in PE.cong (λ X → 1 + X) a
  size-symConv↓Term Γ≡Δ (ne-ins t u x t~u) =
    let B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
    in PE.cong (λ X → 1 + X) (size-sym~↓! Γ≡Δ t~u)
  size-symConv↓Term Γ≡Δ (zero-refl x) = PE.refl
  size-symConv↓Term Γ≡Δ (Ind-refl x) = PE.refl
  size-symConv↓Term Γ≡Δ (ctr-cong x x₁ x₂ x₃ x₄) = PE.cong 1+ (symAll₂Size Γ≡Δ x₄)
    where
    symAll₂Size : ∀ {args args' i Γ Δ}
                → (Γ≡Δ : ⊢ Γ ≡ Δ)
                → (ps : All₂ (λ a a' → Γ ⊢ a [conv↑] a' ∷ Ind i ^ ι ⁰) args args')
                → sizeConv↑TermAll (symAll₂ Γ≡Δ ps) PE.≡ sizeConv↑TermAll ps
    symAll₂Size Γ≡Δ []ₐ = PE.refl
    symAll₂Size Γ≡Δ (p ∷ₐ ps) =
      PE.cong₂ _+_ (size-symConv↑Term Γ≡Δ p) (symAll₂Size Γ≡Δ ps)
  size-symConv↓Term Γ≡Δ (suc-cong x) = PE.cong (λ X → 1 + X) (size-symConv↑Term Γ≡Δ x)
  size-symConv↓Term Γ≡Δ (η-eq l< l<' x x₁ x₂ y y₁ t<>u) =
    PE.cong (λ X → 1 + X) (size-symConv↑Term (Γ≡Δ ∙ refl x) t<>u)

  size-symConv↓ : ∀ {A B Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (A~B : Γ ⊢ A [conv↓] B ^ l) → sizeConv↓ (symConv↓ Γ≡Δ A~B) PE.≡ sizeConv↓ A~B
  size-symConv↓ Γ≡Δ (U-refl PE.refl x₁) = PE.refl
  size-symConv↓ Γ≡Δ (univ x) = PE.cong (λ X → 1 + X) (size-symConv↓Term Γ≡Δ x)
