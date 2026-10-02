{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Properties (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.RedSteps senv equivs
import Definition.Typed.Weakening senv equivs as Twk
import Definition.Equiv senv as Eq
open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product
open import Tools.Sum hiding (id ; sym)
open import Tools.Nat using (Nat; 1+; _<<_)
open import Tools.List using (map; _++_; nth; All; []ₐ; _∷ₐ_; all∈; _∈ₗ_; ∈ₗ-map; ∈ₗ-map-inv)
open import Tools.Maybe using (just; just-injective)
import Tools.List as L
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU
un-univ : ∀ {A r Γ l} → Γ ⊢ A ^ [ r , ι l ] → Γ ⊢ A ∷ Univ r l ^ [ ! , next l ]
un-univ (univ x) = x

-- Inductive types given by a declared name

Indⱼ′ : ∀ {Γ i} → ⊢ Γ → i ∈ₗ SU.indNames senv → Γ ⊢ Ind i ∷ U ⁰ ^ [ ! , ι ¹ ]
Indⱼ′ {i = i} ⊢Γ i∈ with ∈ₗ-map-inv SU.SInd.name senv i i∈
... | ind , PE.refl , ind∈ = Indⱼ ⊢Γ ind∈

-- A well-formed inductive type is declared in [senv]
Ind∈ₜ : ∀ {Γ i A r} → Γ ⊢ Ind i ∷ A ^ r → i ∈ₗ SU.indNames senv
Ind∈ₜ (Indⱼ _ ind∈) = ∈ₗ-map SU.SInd.name ind∈
Ind∈ₜ (conv ⊢I _) = Ind∈ₜ ⊢I

Ind∈ : ∀ {Γ i r} → Γ ⊢ Ind i ^ r → i ∈ₗ SU.indNames senv
Ind∈ (univ ⊢I) = Ind∈ₜ ⊢I

-- Inversion for constructors
inversion-Ctr : ∀ {Γ i j args C r}
  → Γ ⊢ ctr i j args ∷ C ^ r
  → ∃ λ ind → ∃ λ Ts
      → (ind ∈ₗ senv) × (SU.SInd.name ind PE.≡ i)
      × (SU.ctrArgsTypeList ind j PE.≡ just Ts)
      × (Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ])
inversion-Ctr {Γ} {i} {j} {args} ⊢t = go ⊢t PE.refl
  where
    go : ∀ {t A r} → Γ ⊢ t ∷ A ^ r → t PE.≡ ctr i j args
       → ∃ λ ind → ∃ λ Ts
           → (ind ∈ₗ senv) × (SU.SInd.name ind PE.≡ i)
           × (SU.ctrArgsTypeList ind j PE.≡ just Ts)
           × (Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ])
    go (Ctrⱼ {ind = ind′} {j′} {args′} {Ts} _ ind∈ eq ⊢args) e =
      let i≡ , j≡ , args≡ = ctr-PE-injectivity e
      in  ind′ , Ts , ind∈ , i≡
          , PE.subst (λ j → SU.ctrArgsTypeList ind′ j PE.≡ just Ts) j≡ eq
          , PE.subst (λ args → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]) args≡ ⊢args
    go (conv x _) e = go x e
    go (univ _ _) ()
    go (Emptyⱼ _) ()
    go (Πⱼ _ ▹ _ ▹ _ ▹ _) ()
    go (var _ _) ()
    go (lamⱼ _ _ _ _) ()
    go (_▹_▹_▹_∘ⱼ_ _ _ _ _ _) ()
    go (fstⱼ _ _ _ _ _) ()
    go (sndⱼ _ _ _ _ _) ()
    go (Indⱼ _ _) ()
    go (IndRectⱼ _ _ _ _ _) ()
    go (Emptyrecⱼ _ _) ()
    go (Idⱼ _ _ _) ()
    go (Idreflⱼ _) ()
    go (transpⱼ _ _ _ _ _ _) ()
    go (castⱼ _ _ _ _) ()
    go (equiv-eqⱼ _ _) ()

-- Constructor argument types only mention declared inductive types.
ctrArgInds : ∀ {ind j Ts} → ind ∈ₗ senv → SU.ctrArgsTypeList ind j PE.≡ just Ts
           → All (SU.indsInSEnv senv) Ts
ctrArgInds {ind} {j} ind∈ eq =
  lookupAll∈ (lookupAll∈ (proj₂ swf) ind∈) (L.nth-∈ₗ (SU.SInd.ctrArgsTypes ind) j eq)
  where
  lookupAll∈ : ∀ {A : Set} {P : A → Set} {x xs} → All P xs → x ∈ₗ xs → P x
  lookupAll∈ (p ∷ₐ _) L.hereₗ = p
  lookupAll∈ (_ ∷ₐ ps) (L.thereₗ h) = lookupAll∈ ps h

-- Escape context extraction

wfTerm : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → ⊢ Γ
wfTerm (univ <l ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ <l ▹ <l' ▹ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ _ _ F t) with wfTerm t
wfTerm (lamⱼ _ _ F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (_▹_▹_▹_∘ⱼ_ _ _ _ _ ⊢a) = wfTerm ⊢a
wfTerm (fstⱼ A B A' B' e) = wfTerm e
wfTerm (sndⱼ A B A' B' e) = wfTerm e
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (Idⱼ A t u) = wfTerm t
wfTerm (Idreflⱼ t) = wfTerm t
wfTerm (transpⱼ A P t s u e) = wfTerm t
wfTerm (castⱼ A B e t) = wfTerm t
wfTerm (conv t A≡B) = wfTerm t
wfTerm (equiv-eqⱼ ⊢Γ _) = ⊢Γ
wfTerm (Indⱼ ⊢Γ _) = ⊢Γ
wfTerm (Ctrⱼ ⊢Γ _ _ _) = ⊢Γ
wfTerm (IndRectⱼ _ _ _ ⊢t _) = wfTerm ⊢t

wf : ∀ {Γ A r} → Γ ⊢ A ^ r → ⊢ Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (univ A) = wfTerm A

mutual
  wfEqTerm : ∀ {Γ A t u r} → Γ ⊢ t ≡ u ∷ A ^ r → ⊢ Γ
  wfEqTerm (refl t) = wfTerm t
  wfEqTerm (sym t≡u) = wfEqTerm t≡u
  wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
  wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
  wfEqTerm (Π-cong _ _ F F≡H G≡E) = wfEqTerm F≡H
  wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
  wfEqTerm (β-red _ _ F t a) = wfTerm a
  wfEqTerm (η-eq _ _ F f g f0≡g0) = wfTerm f
  wfEqTerm (ctr-cong ⊢Γ _ _ _) = ⊢Γ
  wfEqTerm (IndRect-cong _ _ t≡t' _) = wfEqTerm t≡t'
  wfEqTerm (IndRect-ctr≡ _ _ ⊢P _ _ _) with wf ⊢P
  ... | ⊢Γ ∙ _ = ⊢Γ
  wfEqTerm (Emptyrec-cong A≡A' _ _) = wfEq A≡A'
  wfEqTerm (proof-irrelevance t u) = wfTerm t
  wfEqTerm (Id-cong A t u) = wfEqTerm u
  wfEqTerm (cast-refl A e t) = wfTerm t
  wfEqTerm (cast-cong A B t _ _) = wfEqTerm t
  wfEqTerm (cast-Π A B A' B' e f) = wfTerm f
  wfEqTerm (cast-Ind-refl _ e t) = wfTerm e
  wfEqTerm (cast-equiv _ _ _ _ e t) = wfTerm t

  wfEq : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → ⊢ Γ
  wfEq (univ A≡B) = wfEqTerm A≡B
  wfEq (refl A) = wf A
  wfEq (sym A≡B) = wfEq A≡B
  wfEq (trans A≡B B≡C) = wfEq A≡B

-- Reduction is a subset of conversion
subsetTerm : ∀ {Γ A t u l} → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
subset : ∀ {Γ A B r} → Γ ⊢ A ⇒ B ^ r → Γ ⊢ A ≡ B ^ r

subsetTerm (IndRect-subst ind∈ ⊢P t⇒t' ⊢ms) =
  IndRect-cong ind∈ (refl ⊢P) (subsetTerm t⇒t') (reflAllEq ⊢ms)
  where
    reflAllEq : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → Γ ⊢All ts ≡ ts ∷ As ^ r
    reflAllEq εⱼ = εⱼ
    reflAllEq (consⱼ {r = [ ! , l ]} ⊢t ⊢ts) = consⱼ (refl ⊢t) (reflAllEq ⊢ts)
    reflAllEq (consⱼ {r = [ % , l ]} ⊢t ⊢ts) = consⱼ (proof-irrelevance ⊢t ⊢t) (reflAllEq ⊢ts)
subsetTerm (IndRect-ctr ind∈ eq ⊢P ⊢args ⊢ms nth≡) =
  IndRect-ctr≡ ind∈ eq ⊢P ⊢args ⊢ms nth≡
subsetTerm (app-subst {rA = !} ⊢F ⊢G t⇒u a) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (app-subst {rA = %} ⊢F ⊢G t⇒u a) = app-cong (subsetTerm t⇒u) (proof-irrelevance a a)
subsetTerm (β-red l< l<' A B t a) = β-red l< l<' A t a
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (cast-subst A B e t) = let ⊢Γ = wfEqTerm (subsetTerm A)
                                  in cast-cong (subsetTerm A) (refl B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (subsetTerm A) (refl B))))
subsetTerm (cast-ne-subst A neA B e t) = let ⊢Γ = wfEqTerm (subsetTerm B)
                                  in cast-cong (refl A) (subsetTerm B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl A) (subsetTerm B))))
subsetTerm (cast-Ind-subst ind∈ B e t) = let ⊢Γ = wfEqTerm (subsetTerm B)
                                   in cast-cong (refl (Indⱼ ⊢Γ ind∈)) (subsetTerm B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (Indⱼ ⊢Γ ind∈)) (subsetTerm B))))
subsetTerm (cast-Π-subst A P B e t) = let ⊢Γ = wfTerm A
                                      in cast-cong (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P)) (subsetTerm B) (refl t) e
                                                   (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P)) (subsetTerm B) )))
subsetTerm (cast-Π A B A' B' e f) = cast-Π A B A' B' e f
subsetTerm (cast-Ind-refl ind∈ e t) = cast-Ind-refl ind∈ e t
subsetTerm (cast-equiv A∈ B∈ A≢B H e t) = cast-equiv A∈ B∈ A≢B H e t
subsetTerm (cast-ne-cong A neA B neB e t) = let ⊢Γ = wfTerm A
                                  in cast-cong (refl A) (refl B) (subsetTerm t) e e

subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : ∀ {Γ A t u l } → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : ∀ {Γ A B r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ A ≡ B ^ r
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)

-- Transitivity of reduction

transTerm⇒* : ∀ {Γ A t u v l } → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ u ⇒* v ∷ A ^ l → Γ ⊢ t ⇒* v ∷ A ^ l
transTerm⇒* (id x) y = y
transTerm⇒* (x ⇨ x₁) y = x ⇨ transTerm⇒* x₁ y

trans⇒* : ∀ {Γ A B C r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ B ⇒* C ^ r → Γ ⊢ A ⇒* C ^ r
trans⇒* (id x) y = y
trans⇒* (x ⇨ x₁) y = x ⇨ trans⇒* x₁ y

transTerm:⇒:* : ∀ {Γ A t u v l } → Γ ⊢ t :⇒*: u ∷ A ^ l → Γ ⊢ u :⇒*: v ∷ A ^ l → Γ ⊢ t :⇒*: v ∷ A ^ l
transTerm:⇒:* [[ ⊢t , ⊢u , d ]] [[ ⊢t₁ , ⊢u₁ , d₁ ]] = [[ ⊢t , ⊢u₁ , (transTerm⇒* d d₁) ]]

conv⇒* : ∀ {Γ A B l t u} → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ A ≡ B ^ [ ! , l ] → Γ ⊢ t ⇒* u ∷ B ^ l
conv⇒* (id x) e = id (conv x e)
conv⇒* (x ⇨ D) e = conv x e ⇨ conv⇒* D e

conv:⇒*: : ∀ {Γ A B l t u} → Γ ⊢ t :⇒*: u ∷ A ^ l → Γ ⊢ A ≡ B ^ [ ! , l ] → Γ ⊢ t :⇒*: u ∷ B ^ l
conv:⇒*: [[ ⊢t , ⊢u , d ]] e = [[ (conv ⊢t e) , (conv ⊢u e) , (conv⇒* d e) ]]

-- Can extract left-part of a reduction

redFirstTerm : ∀ {Γ t u A l } → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ∷ A ^ [ ! , l ]
redFirst : ∀ {Γ A B r} → Γ ⊢ A ⇒ B ^ r → Γ ⊢ A ^ r

redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst ⊢F ⊢G t⇒u a) = (λ abs → ⊥-elim (!≢% abs)) ▹ ⊢F ▹ ⊢G ▹ (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red {lA = lA} {lB = lB} lA< lB< ⊢A ⊢B ⊢t ⊢a) = (λ abs → ⊥-elim (!≢% abs)) ▹ un-univ ⊢A ▹ ⊢B ▹ (lamⱼ (λ _ → lA< , lB<) (λ abs → ⊥-elim (!≢% abs)) ⊢A ⊢t) ∘ⱼ ⊢a
redFirstTerm (IndRect-subst ind∈ ⊢P t⇒t' ⊢ms) =
  IndRectⱼ (λ ()) ind∈ ⊢P (redFirstTerm t⇒t') ⊢ms
redFirstTerm (IndRect-ctr ind∈ eq ⊢P ⊢args ⊢ms _) with wf ⊢P
... | ⊢Γ ∙ _ =
  IndRectⱼ (λ ()) ind∈ ⊢P (Ctrⱼ ⊢Γ ind∈ eq ⊢args) ⊢ms
redFirstTerm (cast-subst A B e t) = castⱼ (redFirstTerm A) B e t
redFirstTerm (cast-ne-subst A neA B e t) = castⱼ A (redFirstTerm B) e t
redFirstTerm (cast-Ind-subst ind∈ B e t) = castⱼ (Indⱼ (wfTerm t) ind∈) (redFirstTerm B) e t
redFirstTerm (cast-Π-subst A P B e t) = castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P) (redFirstTerm B) e t
redFirstTerm (cast-Π A B A' B' e f) = castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ B) (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A' ▹ B') e f
redFirstTerm (cast-Ind-refl ind∈ e t) = castⱼ (Indⱼ (wfTerm e) ind∈) (Indⱼ (wfTerm e) ind∈) e t
redFirstTerm (cast-equiv A∈ B∈ A≢B H e t) = castⱼ (Indⱼ′ (wfTerm e) A∈) (Indⱼ′ (wfTerm e) B∈) e t
redFirstTerm (cast-ne-cong K neK L neL e n) = castⱼ K L e (redFirstTerm n)

redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : ∀ {Γ t u A l} → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ t ∷ A ^ [ ! , l ]
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : ∀ {Γ A B r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ A ^ r
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′

-- Neutral types are always small

-- tyNe : ∀ {Γ t r} → Γ ⊢ t ^ r → Neutral t → Γ ⊢ t ∷ (Univ r) ^ !
-- tyNe (univ x) tn = x
-- tyNe (Idⱼ A x y) tn = Idⱼ A x y

-- Neutrals do not weak head reduce

-- IndRect gen-spine uses map: IndRectₙ cannot be matched directly (cf. RelevanceUnicity).
indRectNeRed : ∀ {i lG P t ms} (onIndRectₙ : Neutral t → ⊥)
  → ∀ {s} (n : Neutral s) → s PE.≡ IndRect i lG P t ms → ⊥
indRectNeRed onIndRectₙ (IndRectₙ tn) eq with IndRect-PE-injectivity eq
... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = onIndRectₙ tn
indRectNeRed _ (var _) ()
indRectNeRed _ (∘ₙ _) ()
indRectNeRed _ Emptyrecₙ ()
indRectNeRed _ (castₙ _ _ _) ()
indRectNeRed _ (castnΠₙ _) ()
indRectNeRed _ (castΠₙ _) ()
indRectNeRed _ (castnIndₙ _) ()
indRectNeRed _ (castIndₙ _) ()
indRectNeRed _ (castIndInd≢ₙ _) ()
indRectNeRed _ castIndΠₙ ()
indRectNeRed _ castΠIndₙ ()
indRectNeRed _ castΠΠ%!ₙ ()
indRectNeRed _ (castΠΠ!%ₙ) ()

neRedTerm : ∀ {Γ t u l A} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (n : Neutral t) → ⊥
neRed : ∀ {Γ t u r} (d : Γ ⊢ t ⇒ u ^ r) (n : Neutral t) → ⊥
whnfRedTerm : ∀ {Γ t u A l} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (w : Whnf t) → ⊥
whnfRed : ∀ {Γ A B r} (d : Γ ⊢ A ⇒ B ^ r) (w : Whnf A) → ⊥

neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst _ _ d x) (∘ₙ n) = neRedTerm d n
neRedTerm (β-red _ _ _ x x₁ x₂) (∘ₙ ())
neRedTerm (IndRect-subst {ind} {P} {lG} {t} {ms = ms} _ _ tr _) n =
  indRectNeRed (neRedTerm tr) n PE.refl
neRedTerm (IndRect-ctr {ind} {j} {P} {lG} {args} {ms} _ _ _ _ _ _) n =
  indRectNeRed (λ tn → ctr≢ne tn PE.refl) n PE.refl
neRedTerm (cast-subst tr B e x) (castₙ tn un _) = neRedTerm tr tn
neRedTerm (cast-ne-subst A neA tr e x) (castₙ tn un _) = neRedTerm tr un
neRedTerm (cast-ne-subst A neA tr e x) (castnΠₙ tn) = whnfRedTerm tr Πₙ
neRedTerm (cast-ne-subst A neA tr e x) (castnIndₙ tn) = whnfRedTerm tr Indₙ
neRedTerm (cast-Π-subst A B tr e x) (castΠₙ tn) = neRedTerm tr tn
neRedTerm (cast-Π-subst A B tr e x) (castΠIndₙ) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠₙ tn) = whnfRedTerm tr Πₙ
neRedTerm (cast-subst tr x x₁ x₂) (castnΠₙ tn) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂) (castnIndₙ tn) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂) (castIndₙ tn) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castIndInd≢ₙ _) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castIndΠₙ) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠIndₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-Ind-subst _ tr x x₁) (castIndΠₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-Ind-subst _ tr x x₁) (castIndₙ tn) = neRedTerm tr tn
neRedTerm (cast-Ind-subst _ tr x x₁) (castIndInd≢ₙ _) = whnfRedTerm tr Indₙ
neRedTerm (cast-Π A B A' B' e f) (castₙ () _ _)
neRedTerm (cast-Π A B A' B' e f) (castΠₙ ())
neRedTerm (cast-Ind-refl x x₁ x₂) (castₙ () _ _)
neRedTerm (cast-Ind-refl x x₁ x₂) (castIndₙ ())
neRedTerm (cast-Ind-refl x x₁ x₂) (castIndInd≢ₙ p) = ⊥-elim (p PE.refl)
neRedTerm (cast-equiv _ _ A≢B H e t) (castₙ () _ _)
neRedTerm (cast-equiv _ _ A≢B H e t) (castIndₙ ())
neRedTerm (cast-equiv _ _ A≢B H e t) (castIndInd≢ₙ p) = p H
neRedTerm (cast-subst d x x₁ x₂) castΠΠ%!ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-subst d x x₁ x₂) castΠΠ!%ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-Π-subst x x₁ d x₂ x₃) castΠΠ%!ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-Π-subst x x₁ d x₂ x₃) castΠΠ!%ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-ne-cong K neK L neL e tr) (castₙ X X₁ X₂) = neRedTerm tr X₂

neRed (univ x) N = neRedTerm x N

whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst _ _ d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red _ _ _ x x₁ x₂) (ne (∘ₙ ()))
whnfRedTerm (IndRect-subst {ind} {P} {lG} {t} {ms = ms} _ _ d _) (ne n) =
  indRectNeRed (neRedTerm d) n PE.refl
whnfRedTerm (IndRect-ctr {ind} {j} {P} {lG} {args} {ms} _ _ _ _ _ _) (ne n) =
  indRectNeRed (λ tn → ctr≢ne tn PE.refl) n PE.refl
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castₙ x₃ y _)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castnΠₙ x₃)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castnIndₙ x₃)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castIndₙ x₃)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castΠₙ x₃)) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castIndInd≢ₙ _)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castIndΠₙ) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠIndₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-ne-subst x nex d x₁ x₂) (ne (castₙ x₃ y _)) = neRedTerm d y
whnfRedTerm (cast-ne-subst x nex d x₁ x₂) (ne (castnΠₙ x₃)) =  whnfRedTerm d Πₙ
whnfRedTerm (cast-ne-subst x nex d x₁ x₂) (ne (castnIndₙ x₃)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castIndₙ x₃))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castΠₙ x₃))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castIndInd≢ₙ _))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castIndΠₙ)
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castΠIndₙ)
whnfRedTerm (cast-Ind-subst _ d x x₁) (ne castIndΠₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-Ind-subst _ d x x₁) (ne (castIndₙ x₂)) = neRedTerm d x₂
whnfRedTerm (cast-Ind-subst _ d x x₁) (ne (castIndInd≢ₙ _)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne (castΠₙ x₄)) = neRedTerm d x₄
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠIndₙ) = whnfRedTerm d Indₙ
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castₙ () _ _))
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castΠₙ ()))
whnfRedTerm (cast-Ind-refl x x₁ x₂) (ne (castₙ () _ _))
whnfRedTerm (cast-Ind-refl x x₁ x₂) (ne (castIndₙ ()))
whnfRedTerm (cast-Ind-refl x x₁ x₂) (ne (castIndInd≢ₙ p)) = ⊥-elim (p PE.refl)
whnfRedTerm (cast-equiv _ _ A≢B H e t) (ne (castₙ () _ _))
whnfRedTerm (cast-equiv _ _ A≢B H e t) (ne (castIndₙ ()))
whnfRedTerm (cast-equiv _ _ A≢B H e t) (ne (castIndInd≢ₙ p)) = p H
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠΠ%!ₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠΠ!%ₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠΠ%!ₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠΠ!%ₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-ne-cong K neK L neL e tr) (ne (castₙ x x₁ x₂)) = neRedTerm tr x₂

whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : ∀ {Γ t u A l} (d : Γ ⊢ t ⇒* u ∷ A ^ l) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) Uₙ = PE.refl
whnfRed*Term (id x) Πₙ = PE.refl
whnfRed*Term (id x) Idₙ = PE.refl
whnfRed*Term (id x) Emptyₙ = PE.refl
whnfRed*Term (id x) Indₙ = PE.refl
whnfRed*Term (id x) ctrₙ = PE.refl
whnfRed*Term (id x) lamₙ = PE.refl
whnfRed*Term (id x) (ne x₁) = PE.refl
whnfRed*Term (conv x x₁ ⇨ d) w = ⊥-elim (whnfRedTerm x w)
whnfRed*Term (x ⇨ d) (ne x₁) = ⊥-elim (neRedTerm x x₁)

whnfRed* : ∀ {Γ A B r} (d : Γ ⊢ A ⇒* B ^ r) (w : Whnf A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

-- Whr is deterministic

-- somehow the cases (cast-Π, cast-Π) and (Id-U-ΠΠ, Id-U-ΠΠ) fail if
-- we do not introduce a dummy relevance rA'. This is why we need the two
-- auxiliary functions.
whrDetTerm-aux1 : ∀{Γ t u F lF A A' rA lA lB rA' l B B' e f}
  → (d :  t PE.≡ cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA' ° lA ▹ B' ° lB ° l ^ !) e f)
  → (d′ : Γ ⊢ t ⇒ u ∷ F ^ lF)
  → (lam A' ▹ (let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ l)) ^ l) PE.≡ u
whrDetTerm-aux1 d (conv d' x) = whrDetTerm-aux1 d d'
whrDetTerm-aux1 PE.refl (cast-subst d' x x₁ x₂) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm-aux1 PE.refl (cast-ne-subst x nex d' x₁ x₂) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm-aux1 PE.refl (cast-Π-subst x x₁ d' x₂ x₃) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm-aux1 PE.refl (cast-Π x x₁ x₂ x₃ x₄ x₅) = PE.refl
whrDetTerm-aux1 PE.refl (cast-ne-cong K () L neL e tr)

-- IndRect gen-spine uses map: IndRect-subst/IndRect-ctr cannot be matched directly.
whrDetIndRect-subst : ∀ {Γ t t'} (i : Nat) (P : Term) (lG : Level) (ms : L.List Term)
  (whrDet : ∀ {u A l u' A' l'} → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ⇒ u' ∷ A' ^ l' → u PE.≡ u')
  (d : Γ ⊢ t ⇒ t' ∷ Ind i ^ ι ⁰)
  → ∀ {s u' A' l'} (d' : Γ ⊢ s ⇒ u' ∷ A' ^ l')
  → s PE.≡ IndRect i lG P t ms → IndRect i lG P t' ms PE.≡ u'
whrDetIndRect-subst i P lG ms whrDet d (conv d' _) eq =
  whrDetIndRect-subst i P lG ms whrDet d d' eq
whrDetIndRect-subst i P lG ms whrDet d (IndRect-subst _ _ d' _) eq with IndRect-PE-injectivity eq
... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl =
  PE.cong (λ v → IndRect i lG P v ms) (whrDet d d')
whrDetIndRect-subst i P lG ms whrDet d (IndRect-ctr _ _ _ _ _ _) eq with IndRect-PE-injectivity eq
... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl =
  ⊥-elim (whnfRedTerm d ctrₙ)
whrDetIndRect-subst _ _ _ _ _ _ (app-subst _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (β-red _ _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-subst _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ne-subst _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Ind-subst _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Π-subst _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Π _ _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Ind-refl _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ne-cong _ _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-equiv _ _ _ _ _ _) ()

whrDetTerm : ∀{Γ t u A l u′ A′ l′} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (d′ : Γ ⊢ t ⇒ u′ ∷ A′ ^ l′) → u PE.≡ u′
whrDet : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ⇒ B ^ r) (d′ : Γ ⊢ A ⇒ B′ ^ r') → B PE.≡ B′

whrDetTerm (conv d x) d′ = whrDetTerm d d′
whrDetTerm (app-subst _ _ d x) (app-subst _ _ d′ x₁) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (app-subst _ _ d x) (β-red _ _ _ x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red _ _ _ x x₁ x₂) (app-subst _ _ d' x₃) = ⊥-elim (whnfRedTerm d' lamₙ)
whrDetTerm (β-red _ _ _ x x₁ x₂) (β-red _ _ _ x₃ x₄ x₅) = PE.refl
whrDetTerm (cast-subst d x x₁ x₂) (cast-subst d' x₃ x₄ x₅) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-subst d x x₁ x₂) (cast-Π-subst x₃ x₄ d' x₅ x₆) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Π x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Ind-subst _ d' x₃ x₄) = ⊥-elim (whnfRedTerm d Indₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Ind-refl x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d Indₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-equiv _ _ x₃ H x₄ x₅) = ⊥-elim (whnfRedTerm d Indₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-ne-subst y ney d' x₄ x₅) = ⊥-elim (neRedTerm d ney)
whrDetTerm (cast-ne-subst x nex d x₁ x₂) (cast-subst d' x₃ x₄ x₅) = ⊥-elim (neRedTerm d' nex)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Π-subst x₃ x₄ d' x₅ x₆)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Π x₃ x₄ x₅ x₆ x₇ x₈)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Ind-subst _ d' x₃ x₄)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Ind-refl x₃ x₄ x₅)
whrDetTerm (cast-ne-subst x nex d x₁ x₂) (cast-ne-subst y ney d' x₄ x₅) rewrite whrDetTerm d d' = PE.refl
whrDetTerm {Γ} {u = u} (cast-Ind-subst {ind} {B = B} {e = e} {t = t} _ d _ _) d' =
  goCastIndSubst d' PE.refl
  where
  goCastIndSubst : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' → s PE.≡ cast ⁰ (Ind (SU.SInd.name ind)) B e t → u PE.≡ u'
  goCastIndSubst (conv d'' _) eq = goCastIndSubst d'' eq
  goCastIndSubst (cast-Ind-subst _ d'' _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , A≡ , PE.refl , PE.refl , PE.refl =
    PE.cong₂ (λ A′ B′ → cast ⁰ A′ B′ e t) (PE.sym A≡) (whrDetTerm d d'')
  goCastIndSubst (cast-subst d'' _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndSubst (cast-Ind-refl _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , _ , PE.refl , PE.refl , PE.refl = ⊥-elim (whnfRedTerm d Indₙ)
  goCastIndSubst (app-subst _ _ _ _) ()
  goCastIndSubst (β-red _ _ _ _ _ _) ()
  goCastIndSubst (cast-ne-subst _ neK _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndSubst (cast-Π-subst _ _ _ _ _) ()
  goCastIndSubst (cast-Π _ _ _ _ _ _) ()
  goCastIndSubst (cast-ne-cong _ neK _ _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndSubst (IndRect-subst _ _ _ _) ()
  goCastIndSubst (IndRect-ctr _ _ _ _ _ _) ()
  goCastIndSubst (cast-equiv _ _ _ _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = ⊥-elim (whnfRedTerm d Indₙ)
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-subst d' x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-Π-subst x₄ x₅ d' x₆ x₇) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) d' = whrDetTerm-aux1 (PE.refl) d'
whrDetTerm {Γ} {u = u} (cast-Ind-refl {ind} {e} {t} _ _ _) d' =
  goCastIndCtr d' PE.refl
  where
  goCastIndCtr : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' →
                 s PE.≡ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e t → u PE.≡ u'
  goCastIndCtr (conv d'' _) eq = goCastIndCtr d'' eq
  goCastIndCtr (cast-Ind-refl _ _ _) eq with cast-PE-injectivity eq
  ... | _ , _ , _ , _ , PE.refl = PE.refl
  goCastIndCtr (cast-subst d'' _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndCtr (cast-Ind-subst _ d'' _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , _ , PE.refl , PE.refl , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndCtr (app-subst _ _ _ _) ()
  goCastIndCtr (β-red _ _ _ _ _ _) ()
  goCastIndCtr (cast-ne-subst _ neK _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndCtr (cast-Π-subst _ _ _ _ _) ()
  goCastIndCtr (cast-Π _ _ _ _ _ _) ()
  goCastIndCtr (cast-ne-cong _ neK _ _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndCtr (IndRect-subst _ _ _ _) ()
  goCastIndCtr (IndRect-ctr _ _ _ _ _ _) ()
  goCastIndCtr (cast-equiv _ _ A≢B _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = ⊥-elim (A≢B PE.refl)
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-subst X x₁ x₂ x₃) = ⊥-elim (neRedTerm X neK)
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-ne-subst x₁ x₂ X x₃ x₄) = ⊥-elim (neRedTerm X neL)
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-ne-cong x₁ x₂ x₃ x₄ x₅ X) rewrite whrDetTerm d X = PE.refl
whrDetTerm (cast-subst X x x₁ x₂) (cast-ne-cong K neK L neL e tr) = ⊥-elim (neRedTerm X neK)
whrDetTerm (cast-ne-subst x x₁ X x₂ x₃) (cast-ne-cong K neK L neL e tr) = ⊥-elim (neRedTerm X neL)
whrDetTerm {Γ} {u = u} (cast-equiv {A} {B} {e} {t} A∈ B∈ A≢B H _ _) d' =
  goCastEquiv d' PE.refl
  where
  goCastEquiv : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' → s PE.≡ cast ⁰ (Ind A) (Ind B) e t → u PE.≡ u'
  goCastEquiv (conv d'' _) eq = goCastEquiv d'' eq
  goCastEquiv (cast-equiv A∈′ B∈′ _ H′ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , A≡ , B≡ , PE.refl , PE.refl with Ind-inj A≡ | Ind-inj B≡
  ... | PE.refl | PE.refl =
    PE.cong (λ f → emb-oterm f ∘ t ^ ⁰) (Eq.repr-equiv-fwd-irr equivs A B A∈ B∈ H A∈′ B∈′ H′)
  goCastEquiv (cast-subst d'' _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , _ , _ , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastEquiv (cast-Ind-subst _ d'' _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , _ , PE.refl , _ , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastEquiv (cast-Ind-refl _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , A≡ , B≡ , _ , _ = ⊥-elim (A≢B (PE.trans (PE.sym (Ind-inj A≡)) (Ind-inj B≡)))
  goCastEquiv (cast-ne-subst _ neK _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , _ , _ , _ with neK
  ... | ()
  goCastEquiv (cast-ne-cong _ neK _ _ _ _) eq with cast-PE-injectivity eq
  ... | PE.refl , PE.refl , _ , _ , _ with neK
  ... | ()
  goCastEquiv (app-subst _ _ _ _) ()
  goCastEquiv (β-red _ _ _ _ _ _) ()
  goCastEquiv (cast-Π-subst _ _ _ _ _) ()
  goCastEquiv (cast-Π _ _ _ _ _ _) ()
  goCastEquiv (IndRect-subst _ _ _ _) ()
  goCastEquiv (IndRect-ctr _ _ _ _ _ _) ()
whrDetTerm (IndRect-subst {ind} {P} {lG} {t} {t'} {ms = ms} _ _ d _) d' =
  whrDetIndRect-subst (SU.SInd.name ind) P lG ms whrDetTerm d d' PE.refl
whrDetTerm {Γ} {u = u} (IndRect-ctr {ind} {j} {P} {lG} {args} {ms = ms} ind∈ eqTs _ _ _ nth≡) d' =
  go d' PE.refl
  where
  go : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' →
       s PE.≡ IndRect (SU.SInd.name ind) lG P (ctr (SU.SInd.name ind) j args) ms → u PE.≡ u'
  go (conv d'' _) eq = go d'' eq
  go (IndRect-subst _ _ d'' _) eq with IndRect-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl =
    ⊥-elim (whnfRedTerm d'' ctrₙ)
  go (IndRect-ctr ind∈′ eqTs′ _ _ _ nth≡') eq with IndRect-PE-injectivity eq
  ... | name≡ , _ , _ , _ , _ with SU.name-inj senv (proj₁ swf) ind∈′ ind∈ name≡
  ... | PE.refl with IndRect-PE-injectivity eq
  ... | _ , PE.refl , PE.refl , ctr≡ , PE.refl with ctr-PE-injectivity ctr≡
  ... | _ , PE.refl , PE.refl with just-injective (PE.trans (PE.sym eqTs) eqTs′)
  ... | PE.refl
    rewrite just-injective (PE.trans (PE.sym nth≡) nth≡') = PE.refl
  go (app-subst _ _ _ _) ()
  go (β-red _ _ _ _ _ _) ()
  go (cast-subst _ _ _ _) ()
  go (cast-ne-subst _ _ _ _ _) ()
  go (cast-Ind-subst _ _ _ _) ()
  go (cast-Π-subst _ _ _ _ _) ()
  go (cast-Π _ _ _ _ _ _) ()
  go (cast-Ind-refl _ _ _) ()
  go (cast-ne-cong _ _ _ _ _ _) ()
  go (cast-equiv _ _ _ _ _ _) ()

{-# CATCHALL #-}
whrDetTerm d (conv d′ x₁) = whrDetTerm d d′

whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : ∀{Γ t u A l u′} (d : Γ ⊢ t ↘ u ∷ A ^ l) (d′ : Γ ⊢ t ⇒* u′ ∷ A ^ l)
  → Γ ⊢ u′ ⇒* u ∷ A ^ l
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : ∀{Γ t u A A' l u′ } (d : Γ ⊢ t ↘ u ∷ A ^ l) (d′ : Γ ⊢ t ↘ u′ ∷ A' ^ l) → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ↘ B ^ r) (d′ : Γ ⊢ A ↘ B′ ^ r') → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _ ^ _ )
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Identity of syntactic reduction

idRed:*: : ∀ {Γ A r} → Γ ⊢ A ^ r → Γ ⊢ A :⇒*: A ^ r
idRed:*: A = [[ A , A , id A ]]

idRedTerm:*: : ∀ {Γ A l t} → Γ ⊢ t ∷ A ^ [ ! , l ] → Γ ⊢ t :⇒*: t ∷ A ^ l
idRedTerm:*: t = [[ t , t , id t ]]

-- U cannot be a term

UnotInA : ∀ {A Γ r r'} → Γ ⊢ (Univ r ¹) ∷ A ^ r' → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : ∀ {A B t a Γ r r' r'' r'''}
         → t [ a ] PE.≡ (Univ r ¹)
         → Γ ⊢ a ∷ A ^ r'
         → Γ ∙ A ^ r'' ⊢ t ∷ B ^ r'''
         → ⊥
UnotInA[t] () x₁ (univ 0<1 x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () x₁ (Πⱼ _ ▹ _ ▹ x₂ ▹ x₃)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () x₁ (lamⱼ _ _ x₂ x₃)
UnotInA[t] () x₁ (_ ▹ _ ▹ _ ▹ x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

redU*Term′ : ∀ {A B U′ l Γ r} → U′ PE.≡ (Univ r ¹) → Γ ⊢ A ⇒ U′ ∷ B ^ l → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst _ _ A⇒U x)
redU*Term′ U′≡U (β-red _ _ _ x x₁ x₂) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ () (IndRect-subst _ _ _ _)
redU*Term′ U′≡U (cast-Ind-refl _ _ ⊢t) rewrite U′≡U = UnotInA ⊢t
redU*Term′ {Γ = Γ} {r = r} U′≡U (IndRect-ctr {ind} {j} {args = L.[]} {ms} _ _ _ _ ⊢ms nth≡) =
  look ms _ j ⊢ms nth≡ U′≡U
  where
  look : ∀ ms As n {m} → Γ ⊢All ms ∷ As ^ _ → nth ms n PE.≡ just m → m PE.≡ Univ r ¹ → ⊥
  look L.[] _ n εⱼ ()
  look (_ L.∷ _) _ 0 (consⱼ ⊢m _) PE.refl eq rewrite eq = UnotInA ⊢m
  look (_ L.∷ ms) _ (1+ n) (consⱼ _ ⊢ms) nth≡ eq = look ms _ n ⊢ms nth≡ eq
redU*Term′ U′≡U (IndRect-ctr {ind} {j} {P} {lG} {args = a L.∷ args} {ms} {m} {Ts} _ _ _ _ _ _) =
  apps-∷≢Univ lG m a
    (args ++ map (λ a′ → IndRect (SU.SInd.name ind) lG P a′ ms)
                 (ctrRecArgs (SU.SInd.name ind) Ts (a L.∷ args))) U′≡U

redU*Term : ∀ {A B l Γ r} → Γ ⊢ A ⇒* (Univ r ¹) ∷ B ^ l → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : ∀ {A Γ r l } → Γ ⊢ A ⇒ (Univ r ¹) ^ [ ! , l ] → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : ∀ {A Γ r l } → Γ ⊢ A ⇒* (Univ r ¹) ^ [ ! , l ] → A PE.≡ (Univ r ¹)
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)

-- convertibility for irrelevant terms implies typing

typeInversion : ∀ {t u A l Γ} → Γ ⊢ t ≡ u ∷ A ^ [ % , l ] → Γ ⊢ t ∷ A ^ [ % , l ]
typeInversion (conv X x) = let d = typeInversion X in conv d x
typeInversion (proof-irrelevance x x₁) = x

-- general version of reflexivity, symmetry and transitivity

genRefl : ∀ {A Γ t r l } → Γ ⊢ t ∷ A ^ [ r , l ] → Γ ⊢ t ≡ t ∷ A ^ [ r , l ]
genRefl {r = !} d = refl d
genRefl {r = %} d = proof-irrelevance d d

-- Judgmental instance of the equality relation

genSym : ∀ {k l A Γ r lA } → Γ ⊢ k ≡ l ∷ A ^ [ r , lA ] → Γ ⊢ l ≡ k ∷ A ^ [ r , lA ]
genSym {r = !} = sym
genSym {r = %} (proof-irrelevance x x₁) = proof-irrelevance x₁ x
genSym {r = %} (conv x x₁) = conv (genSym x) x₁

genTrans : ∀ {k l m A r Γ lA } → Γ ⊢ k ≡ l ∷ A ^ [ r , lA ] → Γ ⊢ l ≡ m ∷ A ^ [ r , lA ] → Γ ⊢ k ≡ m ∷ A ^ [ r , lA ]
genTrans {r = !} = trans
genTrans {r = %} (conv X x) (conv Y x₁) = conv (genTrans X (conv Y (trans x₁ (sym x)))) x
genTrans {r = %} (conv X x) (proof-irrelevance x₁ x₂) = proof-irrelevance (conv (typeInversion X) x) x₂
genTrans {r = %} (proof-irrelevance x x₁) (conv Y x₂) = proof-irrelevance x (conv (typeInversion (genSym Y)) x₂)
genTrans {r = %} (proof-irrelevance x x₁) (proof-irrelevance x₂ x₃) = proof-irrelevance x x₃

genVar : ∀ {x A Γ r l } → Γ ⊢ var x ∷ A ^ [ r , l ] → Γ ⊢ var x ≡ var x ∷ A ^ [ r , l ]
genVar {r = !} = refl
genVar {r = %} d = proof-irrelevance d d

toLevelInj : ∀ {l₁ l₁′ : TypeLevel} {l<₁ : l₁′ <∞ l₁} {l₂ l₂′ : TypeLevel} {l<₂ : l₂′ <∞ l₂} →
               toLevel l₁′ PE.≡ toLevel l₂′ → l₁′ PE.≡ l₂′
toLevelInj {.(ι ¹)} {.(ι ⁰)} {emb<} {.(ι ¹)} {.(ι ⁰)} {emb<} e = PE.refl
toLevelInj {.∞} {.(ι ¹)} {∞<} {.(ι ¹)} {.(ι ⁰)} {emb<} ()
toLevelInj {.∞} {.(ι ¹)} {∞<} {.∞} {.(ι ¹)} {∞<} e = PE.refl

redSProp′ : ∀ {Γ A B}
           (D : Γ ⊢ A ⇒* B ∷ SProp ^ next ⁰ )
         → Γ ⊢ A ⇒* B ^ [ % , ι ⁰ ]
redSProp′ (id x) = id (univ x)
redSProp′ (x ⇨ D) = univ x ⇨ redSProp′ D

redSProp : ∀ {Γ A B}
           (D : Γ ⊢ A :⇒*: B ∷ SProp ^ next ⁰ )
         → Γ ⊢ A :⇒*: B ^ [ % , ι ⁰ ]
redSProp [[ ⊢t , ⊢u , d ]] = [[ (univ ⊢t) , (univ ⊢u) , redSProp′ d ]]

un-univ≡ : ∀ {A B r Γ l} → Γ ⊢ A ≡ B ^ [ r , ι l ] → Γ ⊢ A ≡ B ∷ Univ r l ^ [ ! , next l ]
un-univ≡ (univ x) = x
un-univ≡ (refl x) = refl (un-univ x)
un-univ≡ (sym X) = sym (un-univ≡ X)
un-univ≡ (trans X Y) = trans (un-univ≡ X) (un-univ≡ Y)

univ-gen : ∀ {r Γ l} → (⊢Γ : ⊢ Γ) → Γ ⊢ Univ r l ^ [ ! , next l ]
univ-gen {l = ⁰} ⊢Γ = univ (univ 0<1 ⊢Γ )
univ-gen {l = ¹} ⊢Γ = Uⱼ ⊢Γ

un-univ⇒ : ∀ {l Γ A B r} → Γ ⊢ A ⇒ B ^ [ r , ι l ] → Γ ⊢ A ⇒ B ∷ Univ r l ^ next l
un-univ⇒ (univ x) = x

univ⇒* : ∀ {l Γ A B r} → Γ ⊢ A ⇒* B ∷ Univ r l ^ next l → Γ ⊢ A ⇒* B ^ [ r , ι l ]
univ⇒* (id x) = id (univ x)
univ⇒* (x ⇨ D) = univ x ⇨ univ⇒* D

un-univ⇒* : ∀ {l Γ A B r} → Γ ⊢ A ⇒* B ^ [ r , ι l ] → Γ ⊢ A ⇒* B ∷ Univ r l ^ next l
un-univ⇒* (id x) = id (un-univ x)
un-univ⇒* (x ⇨ D) = un-univ⇒ x ⇨ un-univ⇒* D

univ:⇒*: : ∀ {l Γ A B r} →  Γ ⊢ A :⇒*: B ∷ Univ r l ^ next l → Γ ⊢ A :⇒*: B ^ [ r , ι l ]
univ:⇒*: [[ ⊢A , ⊢B , D ]] = [[ (univ ⊢A) , (univ ⊢B) , (univ⇒* D) ]]

un-univ:⇒*: : ∀ {l Γ A B r} → Γ ⊢ A :⇒*: B ^ [ r , ι l ] → Γ ⊢ A :⇒*: B ∷ Univ r l ^ next l
un-univ:⇒*: [[ ⊢A , ⊢B , D ]] = [[ (un-univ ⊢A) , (un-univ ⊢B) , (un-univ⇒* D) ]]

CastRed*Term′ : ∀ {Γ A B X e t}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) A X ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ A X e t ⇒* cast ⁰ B X e t ∷ X ^ ι ⁰
CastRed*Term′ (univ ⊢X) ⊢e ⊢t  (id (univ ⊢A)) = id (castⱼ ⊢A ⊢X ⊢e ⊢t)
CastRed*Term′ (univ ⊢X) ⊢e ⊢t  (univ d ⇨ D) = cast-subst d ⊢X ⊢e ⊢t ⇨
              CastRed*Term′ (univ ⊢X) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (subsetTerm d) (refl ⊢X)) ))
                            (conv ⊢t (subset (univ d))) D

CastRed*Term : ∀ {Γ A B X t e}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) A X ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ∷ U ⁰ ^ next ⁰)
       → Γ ⊢ cast ⁰ A X e t :⇒*: cast ⁰ B X e t ∷ X ^ ι ⁰
CastRed*Term {Γ} {A} {B} (univ ⊢X) ⊢e ⊢t [[ ⊢A , ⊢B , D ]] =
  [[ castⱼ ⊢A ⊢X ⊢e ⊢t , castⱼ ⊢B ⊢X
     (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (subset*Term D) (refl ⊢X)) ))
     (conv ⊢t (univ (subset*Term D))) ,
     CastRed*Term′ (univ ⊢X) ⊢e ⊢t (univ* D) ]]

CastRedR*Term′ : ∀ {Γ A B X e t}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ X ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ X A e t ⇒* cast ⁰ X B e t ∷ A ^ ι ⁰
CastRedR*Term′ (univ ⊢X) neX ⊢e ⊢t  (id (univ ⊢A)) = id (castⱼ ⊢X ⊢A ⊢e ⊢t)
CastRedR*Term′ (univ ⊢X) neX ⊢e ⊢t  (univ d ⇨ D) = cast-ne-subst ⊢X neX d ⊢e ⊢t ⇨
              conv⇒* (CastRedR*Term′ (univ ⊢X) neX (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (refl ⊢X) (subsetTerm d)) ))
                                     ⊢t D) (sym (subset (univ d)))

CastRedR*Term : ∀ {Γ A B X t e}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ X ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ∷ U ⁰ ^ next ⁰)
       → Γ ⊢ cast ⁰ X A e t :⇒*: cast ⁰ X B e t ∷ A ^ ι ⁰
CastRedR*Term {Γ} {A} {B} (univ ⊢X) neX ⊢e ⊢t [[ ⊢A , ⊢B , D ]] =
  [[ castⱼ ⊢X ⊢A ⊢e ⊢t , conv (castⱼ ⊢X ⊢B (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (refl ⊢X) (subset*Term D)) )) ⊢t) (sym (univ (subset*Term D))) ,
     CastRedR*Term′ (univ ⊢X) neX ⊢e ⊢t (univ* D) ]]

CastRedTerm*Term′ : ∀ {Γ X Y e t u}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢Y : Γ ⊢ Y ^ [ ! , ι ⁰ ])
         (neY : Neutral Y)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X Y ^ [ % , ι ⁰ ])
         (D : Γ ⊢ t ⇒* u ∷ X ^ ι ⁰)
       → Γ ⊢ cast ⁰ X Y e t ⇒* cast ⁰ X Y e u ∷ Y ^ ι ⁰
CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e (id ⊢t) = id (castⱼ ⊢X ⊢Y ⊢e ⊢t)
CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e (d ⇨ D) = cast-ne-cong ⊢X neX ⊢Y neY ⊢e d ⇨ CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e D

CastRedTerm*Term : ∀ {Γ X Y t u e}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢Y : Γ ⊢ Y ^ [ ! , ι ⁰ ])
         (neY : Neutral Y)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X Y ^ [ % , ι ⁰ ])
         (D : Γ ⊢ t :⇒*: u ∷ X ^ ι ⁰)
       → Γ ⊢ cast ⁰ X Y e t :⇒*: cast ⁰ X Y e u ∷ Y ^ ι ⁰
CastRedTerm*Term {Γ} {A} {B} (univ ⊢X) neX (univ ⊢Y) neY ⊢e [[ ⊢t , ⊢u , D ]] =
  [[ castⱼ ⊢X ⊢Y ⊢e ⊢t , castⱼ ⊢X ⊢Y ⊢e ⊢u ,
     CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e D ]]







CastRed*TermInd′ : ∀ {Γ i A B e t}
         (i∈ : i ∈ₗ SU.indNames senv)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind i) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Ind i ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Ind i) A e t ⇒* cast ⁰ (Ind i) B e t ∷ A ^ ι ⁰
CastRed*TermInd′ i∈ ⊢e ⊢t  (id (univ ⊢A)) = id (castⱼ (Indⱼ′ (wfTerm ⊢A) i∈) ⊢A ⊢e ⊢t)
CastRed*TermInd′ {i = i} i∈ ⊢e ⊢t  (univ d ⇨ D) with ∈ₗ-map-inv SU.SInd.name senv i i∈
... | ind , PE.refl , ind∈ = cast-Ind-subst ind∈ d ⊢e ⊢t ⇨
                                     conv* (CastRed*TermInd′ i∈
                                             (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (Indⱼ (wfTerm ⊢e) ind∈)) (subsetTerm d))) )
                                             ⊢t D)
                                           (sym (subset (univ d)))

CastRed*TermInd : ∀ {Γ i A B e t}
         (i∈ : i ∈ₗ SU.indNames senv)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind i) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Ind i ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Ind i) A e t :⇒*: cast ⁰ (Ind i) B e t ∷ A ^ ι ⁰
CastRed*TermInd i∈ ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] =
  [[ castⱼ (Indⱼ′ (wfTerm ⊢e) i∈) (un-univ ⊢A) ⊢e ⊢t ,
     conv (castⱼ (Indⱼ′ (wfTerm ⊢e) i∈) (un-univ ⊢B)
          (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (Indⱼ′ (wfTerm ⊢e) i∈)) (subset*Term (un-univ⇒* D)))))
          ⊢t) (sym (subset* D)) ,
       CastRed*TermInd′ i∈ ⊢e ⊢t D ]]

CastRed*TermIndctr : ∀ {Γ ind e t}
         (ind∈ : ind ∈ₗ senv)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e t :⇒*: t ∷ Ind (SU.SInd.name ind) ^ ι ⁰
CastRed*TermIndctr ind∈ ⊢e ⊢t =
  [[ castⱼ (Indⱼ (wfTerm ⊢e) ind∈) (Indⱼ (wfTerm ⊢e) ind∈) ⊢e ⊢t ,
     ⊢t ,
       cast-Ind-refl ind∈ ⊢e ⊢t ⇨ id ⊢t ]]

CastRed*TermIndInd : ∀ {Γ i e t}
         (i∈ : i ∈ₗ SU.indNames senv)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind i) (Ind i) ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Ind i ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Ind i) (Ind i) e t :⇒*: t ∷ Ind i ^ ι ⁰
CastRed*TermIndInd {i = i} i∈ ⊢e ⊢t with ∈ₗ-map-inv SU.SInd.name senv i i∈
... | ind , PE.refl , ind∈ = CastRed*TermIndctr ind∈ ⊢e ⊢t

CastRed*TermΠ′ : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ∷ (Univ rF ⁰) ^ [ ! , next ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ∷ U ⁰ ^ [ ! , next ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A e t ⇒* cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) B e t ∷ A ^ ι ⁰
CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t (id (univ ⊢A)) = id (castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢F ▹ ⊢G) ⊢A ⊢e ⊢t)
CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t (univ d ⇨ D) = cast-Π-subst ⊢F ⊢G d ⊢e ⊢t ⇨
                                     conv* (CastRed*TermΠ′ ⊢F ⊢G
                                                           (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢F ▹ ⊢G)) (subsetTerm d))) )
                                                           ⊢t D)
                                           (sym (subset (univ d)))

CastRed*TermΠ : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ∷ (Univ rF ⁰) ^ [ ! , next ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ∷ U ⁰ ^ [ ! , next ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A e t :⇒*: cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) B e t ∷ A ^ ι ⁰
CastRed*TermΠ ⊢F ⊢G ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] =
  let [Π] = Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢F ▹ ⊢G
  in [[ castⱼ [Π] (un-univ ⊢A) ⊢e ⊢t ,
        conv (castⱼ [Π] (un-univ ⊢B)
          (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl [Π]) (subset*Term (un-univ⇒* D)))))
          ⊢t) (sym (subset* D)) ,
          CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t D ]]

appRed* : ∀ {Γ a t u A B rA lA lB l}
         → Γ     ⊢ A ∷ (Univ rA lA) ^ [ ! , next lA ]
         → Γ ∙ A ^ [ rA , ι lA ] ⊢ B ∷ (U lB) ^ [ ! , next lB ]
         → (⊢a : Γ ⊢ a ∷ A ^ [ rA , ι lA ])
           (D : Γ ⊢ t ⇒* u ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) ^ ι l)
         → Γ ⊢ t ∘ a ^ l ⇒* u ∘ a ^ l ∷ B [ a ] ^ ι lB
appRed* ⊢F ⊢G ⊢a (id x) = id ((λ abs → ⊥-elim (!≢% abs)) ▹ ⊢F ▹ ⊢G ▹ x ∘ⱼ ⊢a)
appRed* ⊢F ⊢G ⊢a (x ⇨ D) = app-subst ⊢F ⊢G x ⊢a ⇨ appRed* ⊢F ⊢G ⊢a D

castΠRed* : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ^ [ rF , ι ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Π F ^ rF ° ⁰ ▹ G ° ⁰  ° ⁰ ^ ! ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A e t ⇒* cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) B e t ∷ A ^ ι ⁰
castΠRed* ⊢F ⊢G ⊢e ⊢t (id (univ ⊢A)) = id (castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ un-univ ⊢F ▹ un-univ ⊢G) ⊢A ⊢e ⊢t)
castΠRed* ⊢F ⊢G ⊢e ⊢t ((univ d) ⇨ D) = cast-Π-subst (un-univ ⊢F) (un-univ ⊢G) d ⊢e ⊢t ⇨ conv* (castΠRed* ⊢F ⊢G
             (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢F))) (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ un-univ ⊢F ▹ un-univ ⊢G)) (subsetTerm d))))
             ⊢t D) (sym (subset (univ d)))

notredUterm* : ∀ {Γ r l l' A B} → Γ ⊢ Univ r l ⇒ A ∷ B ^ l' → ⊥
notredUterm* (conv D x) = notredUterm* D

notredU* : ∀ {Γ r l l' A} → Γ ⊢ Univ r l ⇒ A ^ [ ! , l' ] → ⊥
notredU* (univ x) = notredUterm* x

redU*gen : ∀ {Γ r l r' l' l''} → Γ ⊢ Univ r l ⇒* Univ r' l' ^ [ ! , l'' ] → PE._≡_ {A = Term} (Univ r l) (Univ r' l')
redU*gen (id x) = PE.refl
redU*gen (univ (conv x x₁) ⇨ D) = ⊥-elim (notredUterm* x)

-- Typing of Idsym

Idsymⱼ : ∀ {Γ A l x y e}
       → Γ ⊢ A ∷ U l ^ [ ! , next l ]
       → Γ ⊢ x ∷ A ^ [ ! , ι l ]
       → Γ ⊢ y ∷ A ^ [ ! , ι l ]
       → Γ ⊢ e ∷ Id A x y ^ [ % , ι ⁰ ]
       → Γ ⊢ Idsym A x y e ∷ Id A y x ^ [ % , ι ⁰ ]
Idsymⱼ {Γ} {A} {l} {x} {y} {e} ⊢A ⊢x ⊢y ⊢e =
  let
    ⊢Γ = wfTerm ⊢A
    ⊢A = univ ⊢A
    ⊢P : Γ ∙ A ^ [ ! , ι l ] ⊢ Id (wk1 A) (var 0) (wk1 x) ^ [ % , ι ⁰ ]
    ⊢P = univ (Idⱼ (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢A) (un-univ ⊢A))
      (var (⊢Γ ∙ ⊢A) here)
      (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢A) ⊢x))
    ⊢refl : Γ ⊢ Idrefl A x ∷ Id (wk1 A) (var 0) (wk1 x) [ x ] ^ [ % , ι ⁰ ]
    ⊢refl = PE.subst₂ (λ X Y → Γ ⊢ Idrefl A x ∷ Id X x Y ^ [ % , ι ⁰ ])
      (PE.sym (wk1-singleSubst A x)) (PE.sym (wk1-singleSubst x x))
      (Idreflⱼ ⊢x)
  in PE.subst₂ (λ X Y → Γ ⊢ Idsym A x y e ∷ Id X y Y ^ [ % , ι ⁰ ])
    (wk1-singleSubst A y) (wk1-singleSubst x y)
    (transpⱼ ⊢A ⊢P ⊢x ⊢refl ⊢y ⊢e)

▹▹ⱼ_▹_▹_▹_ : ∀ {Γ F rF lF G lG r l}
             → (r PE.≡ ! → lF ≤ l × lG ≤ l)
             → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
             → Γ ⊢ F ∷ (Univ rF lF) ^ [ ! , next lF ]
             → Γ ⊢ G ∷ (Univ r lG) ^ [ ! , next lG ]
             → Γ ⊢ F ^ rF ° lF ▹▹ G ° lG ° l ^ r ∷ (Univ r l) ^ [ ! , next l ]
▹▹ⱼ lF≤ ▹ lG≤ ▹ F ▹ G = Πⱼ lF≤ ▹ lG≤ ▹ F ▹ un-univ (Twk.wk (Twk.step Twk.id) ((wf (univ F)) ∙ (univ F)) (univ G))
