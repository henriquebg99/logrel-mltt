import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.Soundness (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Typed.EqRelInstance senv swf equivs
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Whnf senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs using (Ind∈Idˡ; Ind∈Idʳ)
open import Tools.Product
open import Tools.List using (All₃; []ₐ; _∷ₐ_; _∈ₗ_)
import Definition.SUntyped as SU
import Tools.PropositionalEquality as PE

mutual

  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑! : ∀ {k l A lA Γ} → Γ ⊢ k ~ l ↑! A ^ lA → Γ ⊢ k ≡ l ∷ A ^ [ ! , lA ]
  soundness~↑! (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _ ^ _) x≡y (refl x)
  soundness~↑! (app-cong {rF = !} k~l x₁) = app-cong (soundness~↓! k~l) (soundnessConv↑Term x₁)
  soundness~↑! (app-cong {rF = %} k~l x₁) = app-cong (soundness~↓! k~l) (let _ , _ , y = soundness~↑% x₁ in y)
  soundness~↑! (Emptyrec-cong x₁ k~l) = let ⊢k , ⊢l , _ = soundness~↑% k~l in
    Emptyrec-cong (soundnessConv↑ x₁) ⊢k ⊢l
  soundness~↑! (cast-cong X x x₁ x₂ x₃) = cast-cong (soundness~↓! X) (sym (soundness~↓! x)) (soundnessConv↓Term x₁) x₂ x₃
  soundness~↑! (cast-Π x X x₁ x₂ x₃) = cast-cong (soundnessConv↑Term x) (sym (soundness~↓! X)) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = cast-cong (soundnessConv↑Term x) (sym (soundnessConv↑Term x₁)) (soundnessConv↑Term x₂) x₃ x₄
  soundness~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = cast-cong (soundnessConv↑Term x) (sym (soundnessConv↑Term x₁)) (soundnessConv↑Term x₂) x₃ x₄
  soundness~↑! (cast-refl x x₁ x₂) =
    let A≡A = soundness~↓! x
        t≡u = soundnessConv↓Term x₁
        _ , ⊢t , _ = syntacticEqTerm t≡u
    in trans (cast-refl A≡A x₂ ⊢t) (conv t≡u (univ A≡A))
  soundness~↑! (cast-refl' x x₁ x₂) =
    let A≡B = sym (soundness~↓! x)
        t≡u = soundnessConv↓Term x₁
        _ , ⊢t , ⊢u = syntacticEqTerm t≡u
    in trans t≡u (conv (sym (cast-refl A≡B x₂ ⊢u)) (sym (univ A≡B)))
  soundness~↑! (cast-neΠ x x₁ x₂ x₃ x₄) = cast-cong (soundness~↓! x₁) (sym (soundnessConv↑Term x)) (soundnessConv↑Term x₂) x₃ x₄
  soundness~↑! (IndRect-cong ind∈ x x₁ x₂) =
    IndRect-cong ind∈ (soundnessConv↑ x) (soundness~↓! x₁) (All₃-soundAll x₂)
  soundness~↑! (cast-neInd x x₁ x₂ x₃) = cast-cong (soundness~↓! x) (refl (Indⱼ′ (wfTerm x₂) (Ind∈Idʳ x₂))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-Ind x x₁ x₂ x₃) = let XX = sym (soundness~↓! x) in cast-cong (refl (Indⱼ′ (wfEqTerm XX) (Ind∈Idˡ x₂))) XX (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-IndΠ x x₁ x₂ x₃) = let XX = (soundnessConv↑Term x) in cast-cong (refl (Indⱼ′ (wfEqTerm XX) (Ind∈Idˡ x₂))) XX (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ΠInd x x₁ x₂ x₃) = let XX = (sym (soundnessConv↑Term x)) in cast-cong XX (refl (Indⱼ′ (wfEqTerm XX) (Ind∈Idʳ x₂))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-IndInd x x₁ x₂ x₃) = let XX = soundnessConv↑Term x₁ in cast-cong (refl (Indⱼ′ (wfEqTerm XX) (Ind∈Idˡ x₂))) (refl (Indⱼ′ (wfEqTerm XX) (Ind∈Idʳ x₂))) (soundnessConv↑Term x₁) x₂ x₃
  
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
  soundnessConv↓Term (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓Term (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' F c c₁) =
    Π-cong l< l<' F (soundnessConv↑Term c) (soundnessConv↑Term c₁)
  soundnessConv↓Term (Id-cong A c c₁) =
    Id-cong (soundnessConv↑Term A) (soundnessConv↑Term c) (soundnessConv↑Term c₁)
  soundnessConv↓Term (Ind-ins x) = soundness~↓! x
  soundnessConv↓Term (Ind-refl ⊢Γ i∈) = refl (Indⱼ′ ⊢Γ i∈)
  soundnessConv↓Term (ctr-cong ⊢Γ ind∈ eq h) = ctr-cong ⊢Γ ind∈ eq (All₃-sound h)
  -- soundnessConv↓Term (Empty-ins x) = soundness~↓% x
  soundnessConv↓Term (ne-ins t u x x₁) =
    let whnfM , neA , neB = ne~↓! x₁
        X = soundness~↓! x₁
        _ , t∷M , _ = syntacticEqTerm X
        _ , M≡A' = neTypeEq neA t∷M t -- soundnessConv↑ M≡A
    in conv X M≡A'
  soundnessConv↓Term (η-eq l< l<' F x x₁ y y₁ c) = η-eq l< l<' F x x₁ (soundnessConv↑Term c)
  soundnessConv↓Term (U-refl PE.refl ⊢Γ) = refl (univ 0<1 ⊢Γ)

  All₃-sound : ∀ {Γ args args' As} →
    All₃ (λ a a' A → Γ ⊢ a [conv↑] a' ∷ A ^ ι ⁰) args args' As →
    All₃ (λ a a' A → Γ ⊢ a ≡ a' ∷ A ^ [ ! , ι ⁰ ]) args args' As
  All₃-sound []ₐ = []ₐ
  All₃-sound (p ∷ₐ ps) = soundnessConv↑Term p ∷ₐ All₃-sound ps

  All₃-soundAll : ∀ {Γ ms ms' As l} →
    All₃ (λ a a' A → Γ ⊢ a [conv↑] a' ∷ A ^ l) ms ms' As →
    Γ ⊢All ms ≡ ms' ∷ As ^ [ ! , l ]
  All₃-soundAll []ₐ = εⱼ
  All₃-soundAll (p ∷ₐ ps) = consⱼ (soundnessConv↑Term p) (All₃-soundAll ps)

app-cong′ : ∀ {Γ k l t v F rF lF G lG lΠ}
          → Γ ⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ
          → Γ ⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ]
          → Γ ⊢ k ∘ t ^ lΠ ~ l ∘ v ^ lΠ ↑ G [ t ] ^ [ ! , ι lG ]
app-cong′ k~l t=v = ~↑! (app-cong k~l t=v)


IndRect-cong′ : ∀ {Γ ind P P' t t' ms ms' lG}
             → ind ∈ₗ senv
             → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P [conv↑] P' ^ [ ! , ι lG ]
             → Γ ⊢ t ~ t' ↓! Ind (SU.SInd.name ind) ^ ι ⁰
             → All₃ (λ m m' A → Γ ⊢ m [conv↑] m' ∷ A ^ ι lG) ms ms' (indRectBranchTyList ind P ! lG)
             → Γ ⊢ IndRect (SU.SInd.name ind) lG P t ms ~ IndRect (SU.SInd.name ind) lG P' t' ms'
                   ↑ (P [ t ]) ^ [ ! , ι lG ]
IndRect-cong′ ind∈ x x₁ x₂ = ~↑! (IndRect-cong ind∈ x x₁ x₂)

Emptyrec-cong′ : ∀ {Γ k l F lF G}
               → Γ ⊢ F [conv↑] G ^ [ ! , ι lF ]
               → Γ ⊢ k ~ l ↑% sEmpty ^ ι ⁰
               → Γ ⊢ Emptyrec lF ⁰ F k ~ Emptyrec lF ⁰ G l ↑ F ^ [ ! , ι lF ]
Emptyrec-cong′ F=G k~l = ~↑! (Emptyrec-cong F=G k~l)
