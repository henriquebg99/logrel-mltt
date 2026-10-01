import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.SoundnessGen (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.Weakening senv equivs as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.ConversionGen senv equivs
open import Definition.Conversion.WhnfGen senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Tools.Product
import Tools.PropositionalEquality as PE
inversion-lam' : ∀ {t F F' G rF lF lG lΠ Γ} → Γ ⊢ lam F ▹ t ^ lΠ ∷ Π F' ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ] →
      Γ ⊢ F ^ [ rF , ι lF ]
    -- × Γ ∙ F ^ [ rF , ι lF ] ⊢ t ∷ G ^ [ ! , ι lG ]
inversion-lam' X with inversion-lam X
... | _ , _ , _ , _ , _ , ⊢F , ⊢G , Π=Π , PE.refl with Π≡A Π=Π Πₙ
... | _ , _ , PE.refl = ⊢F 

mutual
  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑! : ∀ {k l A lA Γ} → Γ ⊢⊢ k ~ l ↑! A ^ lA → Γ ⊢ k ≡ l ∷ A ^ [ ! , lA ]
  soundness~↑! (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _ ^ _) x≡y (refl x)
  soundness~↑! (app-cong {rF = !} k~l x₁) = app-cong (soundness~↓! k~l) (soundnessConv↑Term x₁)
  soundness~↑! (app-cong {rF = %} k~l x₁) = app-cong (soundness~↓! k~l) (let _ , _ , y = soundness~↑% x₁ in y)
  soundness~↑! (Emptyrec-cong x₁ k~l) = let ⊢k , ⊢l , _ = soundness~↑% k~l in
    Emptyrec-cong (soundnessConv↑ x₁) ⊢k ⊢l
  soundness~↑! (cast-cong X x x₁ x₂ x₃ neCast neCast') =
    cast-cong (soundnessConv↓Term X) (sym (soundnessConv↓Term x)) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-refl x x₁ x₂ neCast ne') =
    let A≡A = soundnessConv↓Term x
        t≡u = soundnessConv↓Term x₁
        _ , ⊢t , _ = syntacticEqTerm t≡u
    in trans (cast-refl A≡A x₂ ⊢t) (conv t≡u (univ A≡A))
  soundness~↑! (cast-refl' x x₁ x₂ neCast ne') =
    let A≡B = sym (soundnessConv↓Term x)
        t≡u = soundnessConv↓Term x₁
        _ , ⊢t , ⊢u = syntacticEqTerm t≡u
    in trans t≡u (conv (sym (cast-refl A≡B x₂ ⊢u)) (sym (univ A≡B)))  

  soundness~↑% : ∀ {k l A lA Γ} → Γ ⊢⊢ k ~ l ↑% A ^ lA  →  Γ ⊢ k ∷ A ^ [ % , lA ] × Γ ⊢ l ∷ A ^ [ % , lA ] × Γ ⊢ k ≡ l ∷ A ^ [ % , lA ]
  soundness~↑% (%~↑ ⊢k ⊢l) =  ⊢k , ⊢l , proof-irrelevance ⊢k ⊢l

  soundness~↑ : ∀ {k l A rA lA Γ} → Γ ⊢⊢ k ~ l ↑ A ^ [ rA , lA ] → Γ ⊢ k ≡ l ∷ A ^ [ rA , lA ]
  soundness~↑ (~↑! x) = soundness~↑! x
  soundness~↑ (~↑% x) = let _ , _ , y = soundness~↑% x in y

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓! : ∀ {k l A lA Γ} → Γ ⊢⊢ k ~ l ↓! A ^ lA → Γ ⊢ k ≡ l ∷ A ^ [ ! , lA ]
  soundness~↓! ([~] A₁ D whnfA k~l) = conv (soundness~↑! k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B rA Γ} → Γ ⊢⊢ A [conv↑] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B rA Γ} → Γ ⊢⊢ A [conv↓] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↓ (U-refl PE.refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (univ x₂) = univ (soundnessConv↓Term x₂)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A lA Γ} → Γ ⊢⊢ a [conv↑] b ∷ A ^ lA → Γ ⊢ a ≡ b ∷ A ^ [ ! , lA ]
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A lA Γ} → Γ ⊢⊢ a [conv↓] b ∷ A ^ lA → Γ ⊢ a ≡ b ∷ A ^ [ ! , lA ]
  soundnessConv↓Term (Empty-cong ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓Term (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' c c₁) =
    let F=F = soundnessConv↑Term c
        _ , F , _  = syntacticEqTerm F=F
    in Π-cong l< l<' (univ F) F=F (soundnessConv↑Term c₁)
  soundnessConv↓Term (Id-cong A c c₁) =
    Id-cong (soundnessConv↑Term A) (soundnessConv↑Term c) (soundnessConv↑Term c₁)
  soundnessConv↓Term (ne t u x x₁) =
    let whnfM , neA , neB = ne~↓! x₁
        X = soundness~↓! x₁
        _ , t∷M , _ = syntacticEqTerm X
        _ , M≡A' = neTypeEq neA t∷M t -- soundnessConv↑ M≡A
    in conv X M≡A'
{-  soundnessConv↓Term (lam-cong {G = G} l< l<' ⊢t' c) =
    let t=t' = soundnessConv↑Term c
        _ , ⊢t , ⊢t'' = syntacticEqTerm t=t'
        ⊢ΓF = wfTerm ⊢t
        ⊢Γ , ⊢F = inversion-ctx ⊢ΓF
        -- ⊢F' = inversion-lam' ⊢lt
        ⊢wk1F = T.wk (step id) (⊢Γ ∙ ⊢F) ⊢F
        -- ⊢wk1F' = T.wk (step id) (⊢Γ ∙ ⊢F) ⊢F'
        β-red′ = PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _)
                          (wkSingleSubstId G)
                          (β-red l< l<' ⊢wk1F (T.wkTerm (lift (step id))
                                              (⊢Γ ∙ ⊢F ∙ ⊢wk1F) ⊢t)
                                              (var (⊢Γ ∙ ⊢F) here)) 
        β-red′′ = PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _)
                           (wkSingleSubstId G)
                           (β-red l< l<' ⊢wk1F (T.wkTerm (lift (step id))
                                               (⊢Γ ∙ ⊢F ∙ ⊢wk1F) ⊢t'')
                                               (var (⊢Γ ∙ ⊢F) here)) 
    in η-eq l< l<' ⊢F (lamⱼ (λ x₁ → l< , l<') (λ {()}) ⊢F ⊢t) ⊢t'
                      (trans β-red′ (sym (trans β-red′′ {!!}))) -}
  soundnessConv↓Term (η-eq l< l<' x x₁ y y₁ c) =
    let t=t' = soundnessConv↑Term c
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t'
        ⊢ΓF = wfTerm ⊢t
        ⊢Γ , ⊢F = inversion-ctx ⊢ΓF
    in η-eq l< l<' ⊢F x x₁ t=t'
  soundnessConv↓Term (U-cong PE.refl ⊢Γ) = refl (univ 0<1 ⊢Γ)



app-cong′ : ∀ {Γ k l t v F rF lF G lG lΠ}
          → Γ ⊢⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ
          → Γ ⊢⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ]
          → Γ ⊢⊢ k ∘ t ^ lΠ ~ l ∘ v ^ lΠ ↑ G [ t ] ^ [ ! , ι lG ]
app-cong′ k~l t=v = ~↑! (app-cong k~l t=v)


Emptyrec-cong′ : ∀ {Γ k l F lF G}
               → Γ ⊢⊢ F [conv↑] G ^ [ ! , ι lF ]
               → Γ ⊢⊢ k ~ l ↑% sEmpty ^ ι ⁰
               → Γ ⊢⊢ Emptyrec lF ⁰ F k ~ Emptyrec lF ⁰ G l ↑ F ^ [ ! , ι lF ]
Emptyrec-cong′ F=G k~l = ~↑! (Emptyrec-cong F=G k~l)
