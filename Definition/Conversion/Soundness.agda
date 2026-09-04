open import Definition.Typed.EqRelInstance
import Definition.Equiv as E
module Definition.Conversion.Soundness where
open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq
open import Tools.Product
open import Tools.List using (All₂; []ₐ; _∷ₐ_)
import Tools.PropositionalEquality as PE

mutual

  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑! : ∀ {k l A lA Γ} → Γ ⊢ k ~ l ↑! A ^ lA → Γ ⊢ k ≡ l ∷ A ^ [ ! , lA ]
  soundness~↑! (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _ ^ _) x≡y (refl x)
  soundness~↑! (app-cong {rF = !} k~l x₁) = app-cong (soundness~↓! k~l) (soundnessConv↑Term x₁)
  soundness~↑! (app-cong {rF = %} k~l x₁) = app-cong (soundness~↓! k~l) (let _ , _ , y = soundness~↑% x₁ in y)
  soundness~↑! (natrec-cong x₁ x₂ x₃ k~l) =
    natrec-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                (soundnessConv↑Term x₃) (soundness~↓! k~l)
  soundness~↑! (natrec2-cong x₁ x₂ x₃ k~l) =
    natrec2-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                 (soundnessConv↑Term x₃) (soundness~↓! k~l)
  soundness~↑! (Emptyrec-cong x₁ k~l) = let ⊢k , ⊢l , _ = soundness~↑% k~l in
    Emptyrec-cong (soundnessConv↑ x₁) ⊢k ⊢l
  soundness~↑! (cast-cong X x x₁ x₂ x₃) = cast-cong (soundness~↓! X) (sym (soundness~↓! x)) (soundnessConv↓Term x₁) x₂ x₃
  soundness~↑! (cast-ℕ X x x₁ x₂) = let XX = sym (soundness~↓! X) in cast-cong (refl (ℕⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x) x₁ x₂
  soundness~↑! (cast-ℕ2 X x x₁ x₂) = let XX = sym (soundness~↓! X) in cast-cong (refl (ℕ2ⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x) x₁ x₂
  soundness~↑! (cast-Π x X x₁ x₂ x₃) = cast-cong (soundnessConv↑Term x) (sym (soundness~↓! X)) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-Πℕ x x₁ x₂ x₃) = let XX = (soundnessConv↑Term x) in cast-cong XX (refl (ℕⱼ (wfEqTerm XX))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-Πℕ2 x x₁ x₂ x₃) = let XX = (soundnessConv↑Term x) in cast-cong XX (refl (ℕ2ⱼ (wfEqTerm XX))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ℕΠ x x₁ x₂ x₃) = let XX = (sym (soundnessConv↑Term x)) in cast-cong (refl (ℕⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ℕ2Π x x₁ x₂ x₃) = let XX = (sym (soundnessConv↑Term x)) in cast-cong (refl (ℕ2ⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = cast-cong (soundnessConv↑Term x) (sym (soundnessConv↑Term x₁)) (soundnessConv↑Term x₂) x₃ x₄
  soundness~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = cast-cong (soundnessConv↑Term x) (sym (soundnessConv↑Term x₁)) (soundnessConv↑Term x₂) x₃ x₄
  soundness~↑! (cast-refl x x₁ x₂) =
    let A≡A = soundness~↓! x
        t≡u = soundnessConv↓Term x₁
        _ , ⊢t , _ = syntacticEqTerm t≡u
    in trans (cast-refl A≡A x₂ ⊢t) (conv t≡u (univ A≡A))
  soundness~↑! (castℕ-refl x x₁) =
    let t≡u = soundness~↓! x
        _ , ⊢t , _ = syntacticEqTerm t≡u
    in trans (cast-refl (refl (ℕⱼ (wfTerm ⊢t))) x₁ ⊢t) t≡u
  soundness~↑! (castℕ2-refl x x₁) =
    let t≡u = soundness~↓! x
        _ , ⊢t , _ = syntacticEqTerm t≡u
    in trans (cast-refl (refl (ℕ2ⱼ (wfTerm ⊢t))) x₁ ⊢t) t≡u
  soundness~↑! (cast-refl' x x₁ x₂) =
    let A≡B = sym (soundness~↓! x)
        t≡u = soundnessConv↓Term x₁
        _ , ⊢t , ⊢u = syntacticEqTerm t≡u
    in trans t≡u (conv (sym (cast-refl A≡B x₂ ⊢u)) (sym (univ A≡B)))
  soundness~↑! (castℕ-refl' x x₁) =
    let t≡u = soundness~↓! x
        _ , ⊢t , ⊢u = syntacticEqTerm t≡u
    in trans t≡u (sym (cast-refl (refl (ℕⱼ (wfTerm ⊢t))) x₁ ⊢u))
  soundness~↑! (castℕ2-refl' x x₁) =
    let t≡u = soundness~↓! x
        _ , ⊢t , ⊢u = syntacticEqTerm t≡u
    in trans t≡u (sym (cast-refl (refl (ℕ2ⱼ (wfTerm ⊢t))) x₁ ⊢u))
  soundness~↑! (cast-neℕ x x₁ x₂ x₃) = cast-cong (soundness~↓! x) (refl (ℕⱼ (wfTerm x₂))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-neℕ2 x x₁ x₂ x₃) = cast-cong (soundness~↓! x) (refl (ℕ2ⱼ (wfTerm x₂))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-neΠ x x₁ x₂ x₃ x₄) = cast-cong (soundness~↓! x₁) (sym (soundnessConv↑Term x)) (soundnessConv↑Term x₂) x₃ x₄
  soundness~↑! (IndRect-cong x x₁ x₂) =
    IndRect-cong (soundnessConv↑Term x) (soundness~↓! x₁) x₂
  soundness~↑! (cast-neInd x x₁ x₂ x₃) = cast-cong (soundness~↓! x) (refl (Indⱼ (wfTerm x₂))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-Ind x x₁ x₂ x₃) = let XX = sym (soundness~↓! x) in cast-cong (refl (Indⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (castInd-refl x x₁) =
    let t≡u = soundness~↓! x
        _ , ⊢t , _ = syntacticEqTerm t≡u
    in trans (cast-refl (refl (Indⱼ (wfTerm ⊢t))) x₁ ⊢t) t≡u
  soundness~↑! (cast-IndΠ x x₁ x₂ x₃) = let XX = (soundnessConv↑Term x) in cast-cong (refl (Indⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ΠInd x x₁ x₂ x₃) = let XX = (sym (soundnessConv↑Term x)) in cast-cong XX (refl (Indⱼ (wfEqTerm XX))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-Indℕ x x₁ x₂) = let XX = soundnessConv↑Term x in cast-cong (refl (Indⱼ (wfEqTerm XX))) (refl (ℕⱼ (wfEqTerm XX))) (soundnessConv↑Term x) x₁ x₂
  soundness~↑! (cast-Indℕ2 x x₁ x₂) = let XX = soundnessConv↑Term x in cast-cong (refl (Indⱼ (wfEqTerm XX))) (refl (ℕ2ⱼ (wfEqTerm XX))) (soundnessConv↑Term x) x₁ x₂
  soundness~↑! (cast-ℕInd x x₁ x₂ x₃) = let XX = soundnessConv↑Term x₁ in cast-cong (refl (ℕⱼ (wfEqTerm XX))) (refl (Indⱼ (wfEqTerm XX))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ℕ2Ind x x₁ x₂ x₃) = let XX = soundnessConv↑Term x₁ in cast-cong (refl (ℕ2ⱼ (wfEqTerm XX))) (refl (Indⱼ (wfEqTerm XX))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-IndInd x x₁ x₂ x₃) = let XX = soundnessConv↑Term x₁ in cast-cong (refl (Indⱼ (wfEqTerm XX))) (refl (Indⱼ (wfEqTerm XX))) (soundnessConv↑Term x₁) x₂ x₃
  

  soundness~↑% : ∀ {k l A lA Γ} → Γ ⊢ k ~ l ↑% A ^ lA  →  Γ ⊢ k ∷ A ^ [ % , lA ] × Γ ⊢ l ∷ A ^ [ % , lA ] × Γ ⊢ k ≡ l ∷ A ^ [ % , lA ]
  soundness~↑% (%~↑ ⊢k ⊢l) =  ⊢k , ⊢l , proof-irrelevance ⊢k ⊢l

  soundness~↑ : ∀ {k l A rA lA Γ} → Γ ⊢ k ~ l ↑ A ^ [ rA , lA ] → Γ ⊢ k ≡ l ∷ A ^ [ rA , lA ]
  soundness~↑ (~↑! x) = soundness~↑! x
  soundness~↑ (~↑% x) = let _ , _ , y = soundness~↑% x in y

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓! : ∀ {k l A lA Γ} → Γ ⊢ k ~ l ↓! A ^ lA → Γ ⊢ k ≡ l ∷ A ^ [ ! , lA ]
  soundness~↓! ([~] A₁ D whnfA k~l) = conv (soundness~↑! k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B rA Γ} → Γ ⊢ A [conv↑] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B rA Γ} → Γ ⊢ A [conv↓] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↓ (U-refl PE.refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (univ x₂) = univ (soundnessConv↓Term x₂)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A lA Γ} → Γ ⊢ a [conv↑] b ∷ A ^ lA → Γ ⊢ a ≡ b ∷ A ^ [ ! , lA ]
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A lA Γ} → Γ ⊢ a [conv↓] b ∷ A ^ lA → Γ ⊢ a ≡ b ∷ A ^ [ ! , lA ]
  soundnessConv↓Term (ne x) = soundness~↓! x
  soundnessConv↓Term (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓Term (ℕ2-refl ⊢Γ) = refl (ℕ2ⱼ ⊢Γ)
  soundnessConv↓Term (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓Term (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' F c c₁) =
    Π-cong l< l<' F (soundnessConv↑Term c) (soundnessConv↑Term c₁)
  soundnessConv↓Term (Id-cong A c c₁) =
    Id-cong (soundnessConv↑Term A) (soundnessConv↑Term c) (soundnessConv↑Term c₁)
  soundnessConv↓Term (ℕ-ins x) = soundness~↓! x
  soundnessConv↓Term (ℕ2-ins x) = soundness~↓! x
  soundnessConv↓Term (Ind-ins x) = soundness~↓! x
  soundnessConv↓Term (Ind-refl ⊢Γ) = refl (Indⱼ ⊢Γ)
  soundnessConv↓Term (ctr-cong ⊢Γ len h) = ctr-cong ⊢Γ len (All₂-sound h)
  -- soundnessConv↓Term (Empty-ins x) = soundness~↓% x
  soundnessConv↓Term (ne-ins t u x x₁) =
    let whnfM , neA , neB = ne~↓! x₁
        X = soundness~↓! x₁
        _ , t∷M , _ = syntacticEqTerm X
        _ , M≡A' = neTypeEq neA t∷M t -- soundnessConv↑ M≡A
    in conv X M≡A'
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (zero2-refl ⊢Γ) = refl (zero2ⱼ ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (suc2-cong c) = suc2-cong (soundnessConv↑Term c)
  soundnessConv↓Term (η-eq l< l<' F x x₁ y y₁ c) = η-eq l< l<' F x x₁ (soundnessConv↑Term c)
  soundnessConv↓Term (U-refl PE.refl ⊢Γ) = refl (univ 0<1 ⊢Γ)

  All₂-sound : ∀ {Γ args args' i} →
    All₂ (λ a a' → Γ ⊢ a [conv↑] a' ∷ Ind i ^ ι ⁰) args args' →
    All₂ (λ a a' → Γ ⊢ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ]) args args'
  All₂-sound []ₐ = []ₐ
  All₂-sound (p ∷ₐ ps) = soundnessConv↑Term p ∷ₐ All₂-sound ps



app-cong′ : ∀ {Γ k l t v F rF lF G lG lΠ}
          → Γ ⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ
          → Γ ⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ]
          → Γ ⊢ k ∘ t ^ lΠ ~ l ∘ v ^ lΠ ↑ G [ t ] ^ [ ! , ι lG ]
app-cong′ k~l t=v = ~↑! (app-cong k~l t=v)

natrec-cong′ : ∀ {Γ k l h g a b F lF G}
             → Γ ∙ ℕ ^ [ ! , ι ⁰ ]  ⊢ F [conv↑] G ^ [ ! , ι lF ]
             → Γ ⊢ a [conv↑] b ∷ F [ zero ] ^ ι lF
             → Γ ⊢ h [conv↑] g ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ ι lF
             → Γ ⊢ k ~ l ↓! ℕ ^ ι ⁰
             → Γ ⊢ natrec lF F a h k ~ natrec lF G b g l ↑ F [ k ] ^ [ ! , ι lF ]
natrec-cong′ F=G a=b h=g k~l = ~↑! (natrec-cong F=G a=b h=g k~l)

natrec2-cong′ : ∀ {Γ k l h g a b F lF G}
             → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ]  ⊢ F [conv↑] G ^ [ ! , ι lF ]
             → Γ ⊢ a [conv↑] b ∷ F [ zero2 ] ^ ι lF
             → Γ ⊢ h [conv↑] g ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ ι lF
             → Γ ⊢ k ~ l ↓! ℕ2 ^ ι ⁰
             → Γ ⊢ natrec2 lF F a h k ~ natrec2 lF G b g l ↑ F [ k ] ^ [ ! , ι lF ]
natrec2-cong′ F=G a=b h=g k~l = ~↑! (natrec2-cong F=G a=b h=g k~l)

IndRect-cong′ : ∀ {Γ i P P' lG t t' ms ms'}
             → Γ ⊢ P [conv↑] P' ∷ Π Ind i ^ ! ° ⁰ ▹ Univ ! lG ° ¹ ° ¹ ^ ! ^ ι ¹
             → Γ ⊢ t ~ t' ↓! Ind i ^ ι ⁰
             → Γ ⊢All ms ≡ ms' ∷ indRectBranchTyList i P ! lG ^ [ ! , ι lG ]
             → Γ ⊢ IndRect i lG P t ms ~ IndRect i lG P' t' ms' ↑ (P ∘ t ^ ¹) ^ [ ! , ι lG ]
IndRect-cong′ x x₁ x₂ = ~↑! (IndRect-cong x x₁ x₂)

Emptyrec-cong′ : ∀ {Γ k l F lF G}
               → Γ ⊢ F [conv↑] G ^ [ ! , ι lF ]
               → Γ ⊢ k ~ l ↑% sEmpty ^ ι ⁰
               → Γ ⊢ Emptyrec lF ⁰ F k ~ Emptyrec lF ⁰ G l ↑ F ^ [ ! , ι lF ]
Emptyrec-cong′ F=G k~l = ~↑! (Emptyrec-cong F=G k~l)
