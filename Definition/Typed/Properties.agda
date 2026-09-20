import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Properties (senv : SI.SEnv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv
open import Definition.Untyped.Properties senv
open import Definition.Typed senv equivs
open import Definition.Typed.RedSteps senv equivs
import Definition.Typed.Weakening senv equivs as Twk
open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product
open import Tools.Sum hiding (id ; sym)
open import Tools.Nat using (Nat; 1+; _<<_)
open import Tools.List using (map; _++_; nth; All; []ₐ; _∷ₐ_; all∈; _∈ₗ_)
open import Tools.Maybe using (just; just-injective)
import Tools.List as L
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU
un-univ : ∀ {A r Γ l} → Γ ⊢ A ^ [ r , ι l ] → Γ ⊢ A ∷ Univ r l ^ [ ! , next l ]
un-univ (univ x) = x

-- Escape context extraction

wfTerm : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → ⊢ Γ
wfTerm (univ <l ⊢Γ) = ⊢Γ
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ <l ▹ <l' ▹ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ _ _ F t) with wfTerm t
wfTerm (lamⱼ _ _ F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (_▹_▹_▹_∘ⱼ_ _ _ _ _ ⊢a) = wfTerm ⊢a
wfTerm (fstⱼ A B A' B' e) = wfTerm e
wfTerm (sndⱼ A B A' B' e) = wfTerm e
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ _ F z s n) = wfTerm z
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (Idⱼ A t u) = wfTerm t
wfTerm (Idreflⱼ t) = wfTerm t
wfTerm (transpⱼ A P t s u e) = wfTerm t
wfTerm (castⱼ A B e t) = wfTerm t
wfTerm (conv t A≡B) = wfTerm t
wfTerm (equiv-eqⱼ ⊢Γ) = ⊢Γ
wfTerm (Indⱼ ⊢Γ) = ⊢Γ
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
  wfEqTerm (suc-cong n) = wfEqTerm n
  wfEqTerm (ctr-cong ⊢Γ _ _ _ _) = ⊢Γ
  wfEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
  wfEqTerm (natrec-zero F z s) = wfTerm z
  wfEqTerm (natrec-suc n F z s) = wfTerm n
  wfEqTerm (IndRect-cong _ _ t≡t' _) = wfEqTerm t≡t'
  wfEqTerm (IndRect-ctr≡ _ _ ⊢P _ _ _) with wf ⊢P
  ... | ⊢Γ ∙ _ = ⊢Γ
  wfEqTerm (Emptyrec-cong A≡A' _ _) = wfEq A≡A'
  wfEqTerm (proof-irrelevance t u) = wfTerm t
  wfEqTerm (Id-cong A t u) = wfEqTerm u
  wfEqTerm (cast-refl A e t) = wfTerm t
  wfEqTerm (cast-cong A B t _ _) = wfEqTerm t
  wfEqTerm (cast-Π A B A' B' e f) = wfTerm f
  wfEqTerm (cast-ℕ-0 e) = wfTerm e
  wfEqTerm (cast-ℕ-S e n) = wfTerm n
  wfEqTerm (cast-Ind-ctr _ _ e args) = wfTerm e

  wfEq : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → ⊢ Γ
  wfEq (univ A≡B) = wfEqTerm A≡B
  wfEq (refl A) = wf A
  wfEq (sym A≡B) = wfEq A≡B
  wfEq (trans A≡B B≡C) = wfEq A≡B

-- Reduction is a subset of conversion
subsetTerm : ∀ {Γ A t u l} → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
subset : ∀ {Γ A B r} → Γ ⊢ A ⇒ B ^ r → Γ ⊢ A ≡ B ^ r

subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
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
subsetTerm (cast-ℕ-subst B e t) = let ⊢Γ = wfEqTerm (subsetTerm B)
                                  in cast-cong (refl (ℕⱼ (wfTerm t))) (subsetTerm B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (ℕⱼ ⊢Γ)) (subsetTerm B))))
subsetTerm (cast-Ind-subst {i = i} B e t) = let ⊢Γ = wfEqTerm (subsetTerm B)
                                   in cast-cong (refl (Indⱼ ⊢Γ)) (subsetTerm B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (Indⱼ ⊢Γ)) (subsetTerm B))))
subsetTerm (cast-Π-subst A P B e t) = let ⊢Γ = wfTerm A
                                      in cast-cong (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P)) (subsetTerm B) (refl t) e
                                                   (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P)) (subsetTerm B) )))
subsetTerm (cast-Π A B A' B' e f) = cast-Π A B A' B' e f
subsetTerm (cast-ℕ-0 e) = cast-ℕ-0 e
subsetTerm (cast-ℕ-S e n) = cast-ℕ-S e n
subsetTerm (cast-Ind-ctr ind∈ eq e args) = cast-Ind-ctr ind∈ eq e args
subsetTerm (cast-ℕ-cong e n) = let ⊢Γ = wfTerm e
                                   ⊢ℕ = ℕⱼ ⊢Γ
                               in cast-cong (refl ⊢ℕ) (refl ⊢ℕ) (subsetTerm n) e e
subsetTerm (cast-Ind-cong {i = i} e n) = let ⊢Γ = wfTerm e
                                             ⊢Ind = Indⱼ ⊢Γ
                                         in cast-cong (refl ⊢Ind) (refl ⊢Ind) (subsetTerm n) e e
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
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc n F z s) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s (sucⱼ n)
redFirstTerm (IndRect-subst ind∈ ⊢P t⇒t' ⊢ms) =
  IndRectⱼ (λ ()) ind∈ ⊢P (redFirstTerm t⇒t') ⊢ms
redFirstTerm (IndRect-ctr ind∈ eq ⊢P ⊢args ⊢ms _) with wf ⊢P
... | ⊢Γ ∙ _ =
  IndRectⱼ (λ ()) ind∈ ⊢P (Ctrⱼ ⊢Γ ind∈ eq ⊢args) ⊢ms
redFirstTerm (cast-subst A B e t) = castⱼ (redFirstTerm A) B e t
redFirstTerm (cast-ne-subst A neA B e t) = castⱼ A (redFirstTerm B) e t
redFirstTerm (cast-ℕ-subst B e t) = castⱼ (ℕⱼ (wfTerm t)) (redFirstTerm B) e t
redFirstTerm (cast-Ind-subst {i = i} B e t) = castⱼ (Indⱼ (wfTerm t)) (redFirstTerm B) e t
redFirstTerm (cast-Π-subst A P B e t) = castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P) (redFirstTerm B) e t
redFirstTerm (cast-Π A B A' B' e f) = castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ B) (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A' ▹ B') e f
redFirstTerm (cast-ℕ-0 e) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (zeroⱼ (wfTerm e))
redFirstTerm (cast-ℕ-S e n) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (sucⱼ n)
redFirstTerm (cast-ℕ-cong e n) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (redFirstTerm n)
redFirstTerm (cast-Ind-ctr ind∈ eq e args) = castⱼ (Indⱼ (wfTerm e)) (Indⱼ (wfTerm e)) e (Ctrⱼ (wfTerm e) ind∈ eq args)
redFirstTerm (cast-Ind-cong {i = i} e n) = castⱼ (Indⱼ (wfTerm e)) (Indⱼ (wfTerm e)) e (redFirstTerm n)
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
indRectNeRed _ (natrecₙ _) ()
indRectNeRed _ Emptyrecₙ ()
indRectNeRed _ (castₙ _ _ _) ()
indRectNeRed _ (castnℕₙ _) ()
indRectNeRed _ (castnΠₙ _) ()
indRectNeRed _ (castℕₙ _) ()
indRectNeRed _ (castΠₙ _) ()
indRectNeRed _ (castℕℕₙ _) ()
indRectNeRed _ (castnIndₙ _) ()
indRectNeRed _ (castIndₙ _) ()
indRectNeRed _ (castIndIndₙ _) ()
indRectNeRed _ (castIndInd≢ₙ _) ()
indRectNeRed _ castℕΠₙ ()
indRectNeRed _ castΠℕₙ ()
indRectNeRed _ castIndΠₙ ()
indRectNeRed _ castΠIndₙ ()
indRectNeRed _ castIndℕₙ ()
indRectNeRed _ castℕIndₙ ()
indRectNeRed _ castΠΠ%!ₙ ()
indRectNeRed _ (castΠΠ!%ₙ) ()

neRedTerm : ∀ {Γ t u l A} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (n : Neutral t) → ⊥
neRed : ∀ {Γ t u r} (d : Γ ⊢ t ⇒ u ^ r) (n : Neutral t) → ⊥
whnfRedTerm : ∀ {Γ t u A l} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (w : Whnf t) → ⊥
whnfRed : ∀ {Γ A B r} (d : Γ ⊢ A ⇒ B ^ r) (w : Whnf A) → ⊥

neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst _ _ d x) (∘ₙ n) = neRedTerm d n
neRedTerm (β-red _ _ _ x x₁ x₂) (∘ₙ ())
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
neRedTerm (natrec-subst x x₁ x₂ tr) (natrecₙ tn) = neRedTerm tr tn
neRedTerm (IndRect-subst {ind} {P} {lG} {t} {ms = ms} _ _ tr _) n =
  indRectNeRed (neRedTerm tr) n PE.refl
neRedTerm (IndRect-ctr {ind} {j} {P} {lG} {args} {ms} _ _ _ _ _ _) n =
  indRectNeRed (λ tn → Ctr≢ne tn PE.refl) n PE.refl
neRedTerm (cast-subst tr B e x) (castₙ tn un _) = neRedTerm tr tn
neRedTerm (cast-ne-subst A neA tr e x) (castₙ tn un _) = neRedTerm tr un
neRedTerm (cast-ne-subst A neA tr e x) (castnΠₙ tn) = whnfRedTerm tr Πₙ
neRedTerm (cast-ne-subst A neA tr e x) (castnℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-ne-subst A neA tr e x) (castnIndₙ tn) = whnfRedTerm tr Indₙ
neRedTerm (cast-Π-subst A B tr e x) (castΠₙ tn) = neRedTerm tr tn
neRedTerm (cast-Π-subst A B tr e x) (castΠℕₙ) = whnfRedTerm tr ℕₙ
neRedTerm (cast-Π-subst A B tr e x) (castΠIndₙ) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠₙ tn) = whnfRedTerm tr Πₙ
neRedTerm (cast-subst tr x x₁ x₂) (castnℕₙ tn) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂) (castnΠₙ tn) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂) (castℕℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castnIndₙ tn) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂) (castIndₙ tn) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castIndIndₙ tn) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castIndInd≢ₙ _) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castℕΠₙ) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠℕₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-subst tr x x₁ x₂) (castIndΠₙ) = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠIndₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-subst tr x x₁ x₂) castIndℕₙ = whnfRedTerm tr Indₙ
neRedTerm (cast-subst tr x x₁ x₂) castℕIndₙ = whnfRedTerm tr ℕₙ
neRedTerm (cast-ℕ-subst tr x x₁) (castℕₙ tn) = neRedTerm tr tn
neRedTerm (cast-ℕ-subst tr x x₁) (castℕℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-ℕ-subst tr x x₁) (castℕΠₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-ℕ-subst tr x x₁) castℕIndₙ = whnfRedTerm tr Indₙ
neRedTerm (cast-Ind-subst tr x x₁) (castIndΠₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-Ind-subst tr x x₁) (castIndₙ tn) = neRedTerm tr tn
neRedTerm (cast-Ind-subst tr x x₁) (castIndIndₙ tn) = whnfRedTerm tr Indₙ
neRedTerm (cast-Ind-subst tr x x₁) (castIndInd≢ₙ _) = whnfRedTerm tr Indₙ
neRedTerm (cast-Ind-subst tr x x₁) castIndℕₙ = whnfRedTerm tr ℕₙ
neRedTerm (cast-Π A B A' B' e f) (castₙ () _ _)
neRedTerm (cast-Π A B A' B' e f) (castΠₙ ())
neRedTerm (cast-ℕ-0 x) (castₙ () _ _)
neRedTerm (cast-ℕ-0 x) (castℕₙ ())
neRedTerm (cast-ℕ-0 x) (castℕℕₙ ())
neRedTerm (cast-ℕ-S x x₁) (castₙ () _ _)
neRedTerm (cast-ℕ-S x x₁) (castℕₙ ())
neRedTerm (cast-ℕ-S x x₁) (castℕℕₙ ())
neRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (castₙ () _ _)
neRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (castIndₙ ())
neRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (castIndIndₙ ())
neRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (castIndInd≢ₙ p) = ⊥-elim (p PE.refl)
neRedTerm (cast-ℕ-cong x x₁) (castₙ () _ _)
neRedTerm (cast-ℕ-cong x x₁) (castℕₙ ())
neRedTerm (cast-ℕ-cong x x₁) (castℕℕₙ t) = neRedTerm x₁ t
neRedTerm (cast-Ind-cong x x₁) (castₙ () _ _)
neRedTerm (cast-Ind-cong x x₁) (castIndₙ ())
neRedTerm (cast-Ind-cong x x₁) (castIndIndₙ t) = neRedTerm x₁ t
neRedTerm (cast-Ind-cong x x₁) (castIndInd≢ₙ p) = ⊥-elim (p PE.refl)
neRedTerm (cast-subst d x x₁ x₂) castΠΠ%!ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-subst d x x₁ x₂) castΠΠ!%ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-Π-subst x x₁ d x₂ x₃) castΠΠ%!ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-Π-subst x x₁ d x₂ x₃) castΠΠ!%ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-ne-cong K neK L neL e tr) (castₙ X X₁ X₂) = neRedTerm tr X₂

neRed (univ x) N = neRedTerm x N

whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst _ _ d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red _ _ _ x x₁ x₂) (ne (∘ₙ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
whnfRedTerm (IndRect-subst {ind} {P} {lG} {t} {ms = ms} _ _ d _) (ne n) =
  indRectNeRed (neRedTerm d) n PE.refl
whnfRedTerm (IndRect-ctr {ind} {j} {P} {lG} {args} {ms} _ _ _ _ _ _) (ne n) =
  indRectNeRed (λ tn → Ctr≢ne tn PE.refl) n PE.refl
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castₙ x₃ y _)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castnℕₙ x₃)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castnΠₙ x₃)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castnIndₙ x₃)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castℕₙ x₃)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castIndₙ x₃)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castΠₙ x₃)) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castℕℕₙ x₃)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castIndIndₙ x₃)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castIndInd≢ₙ _)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castℕΠₙ) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠℕₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castIndΠₙ) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠIndₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castIndℕₙ) = whnfRedTerm d Indₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castℕIndₙ) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-ne-subst x nex d x₁ x₂) (ne (castₙ x₃ y _)) = neRedTerm d y
whnfRedTerm (cast-ne-subst x nex d x₁ x₂) (ne (castnℕₙ x₃)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-ne-subst x nex d x₁ x₂) (ne (castnΠₙ x₃)) =  whnfRedTerm d Πₙ
whnfRedTerm (cast-ne-subst x nex d x₁ x₂) (ne (castnIndₙ x₃)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castℕₙ x₃))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castIndₙ x₃))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castΠₙ x₃))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castℕℕₙ x₃))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castIndIndₙ x₃))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne (castIndInd≢ₙ _))
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castℕΠₙ)
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castΠℕₙ)
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castIndΠₙ)
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castΠIndₙ)
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castIndℕₙ)
whnfRedTerm (cast-ne-subst x () d x₁ x₂) (ne castℕIndₙ)
whnfRedTerm (cast-ℕ-subst d x x₁) (ne (castℕₙ x₂)) = neRedTerm d x₂
whnfRedTerm (cast-ℕ-subst d x x₁) (ne (castℕℕₙ x₂)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-ℕ-subst d x x₁) (ne castℕΠₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-ℕ-subst d x x₁) (ne castℕIndₙ) = whnfRedTerm d Indₙ
whnfRedTerm (cast-Ind-subst d x x₁) (ne castIndΠₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-Ind-subst d x x₁) (ne (castIndₙ x₂)) = neRedTerm d x₂
whnfRedTerm (cast-Ind-subst d x x₁) (ne (castIndIndₙ x₂)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-Ind-subst d x x₁) (ne (castIndInd≢ₙ _)) = whnfRedTerm d Indₙ
whnfRedTerm (cast-Ind-subst d x x₁) (ne castIndℕₙ) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne (castΠₙ x₄)) = neRedTerm d x₄
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠℕₙ) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠIndₙ) = whnfRedTerm d Indₙ
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castₙ () _ _))
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castΠₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castₙ () _ _))
whnfRedTerm (cast-ℕ-0 x) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castℕℕₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castₙ () _ _))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castℕℕₙ ()))
whnfRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (ne (castₙ () _ _))
whnfRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (ne (castIndₙ ()))
whnfRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (ne (castIndIndₙ ()))
whnfRedTerm (cast-Ind-ctr x₆ x x₁ x₂) (ne (castIndInd≢ₙ p)) = ⊥-elim (p PE.refl)
whnfRedTerm (cast-ℕ-cong x x₁) (ne (castₙ () _ _))
whnfRedTerm (cast-ℕ-cong x x₁) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-cong x x₁) (ne (castℕℕₙ t)) = neRedTerm x₁ t
whnfRedTerm (cast-Ind-cong x x₁) (ne (castₙ () _ _))
whnfRedTerm (cast-Ind-cong x x₁) (ne (castIndₙ ()))
whnfRedTerm (cast-Ind-cong x x₁) (ne (castIndIndₙ t)) = neRedTerm x₁ t
whnfRedTerm (cast-Ind-cong x x₁) (ne (castIndInd≢ₙ p)) = ⊥-elim (p PE.refl)
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
whnfRed*Term (id x) ℕₙ = PE.refl
whnfRed*Term (id x) Emptyₙ = PE.refl
whnfRed*Term (id x) Indₙ = PE.refl
whnfRed*Term (id x) ctrₙ = PE.refl
whnfRed*Term (id x) lamₙ = PE.refl
whnfRed*Term (id x) zeroₙ = PE.refl
whnfRed*Term (id x) sucₙ = PE.refl
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
whrDetIndRect-subst _ _ _ _ _ _ (natrec-subst _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (natrec-zero _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (natrec-suc _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-subst _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ne-subst _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ℕ-subst _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Ind-subst _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Π-subst _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Π _ _ _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ℕ-0 _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ℕ-S _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ℕ-cong _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Ind-ctr _ _ _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-Ind-cong _ _) ()
whrDetIndRect-subst _ _ _ _ _ _ (cast-ne-cong _ _ _ _ _ _) ()

whrDetTerm : ∀{Γ t u A l u′ A′ l′} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (d′ : Γ ⊢ t ⇒ u′ ∷ A′ ^ l′) → u PE.≡ u′
whrDet : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ⇒ B ^ r) (d′ : Γ ⊢ A ⇒ B′ ^ r') → B PE.≡ B′

whrDetTerm (conv d x) d′ = whrDetTerm d d′
whrDetTerm (app-subst _ _ d x) (app-subst _ _ d′ x₁) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (app-subst _ _ d x) (β-red _ _ _ x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red _ _ _ x x₁ x₂) (app-subst _ _ d' x₃) = ⊥-elim (whnfRedTerm d' lamₙ)
whrDetTerm (β-red _ _ _ x x₁ x₂) (β-red _ _ _ x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d') = ⊥-elim (whnfRedTerm d' zeroₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d') = ⊥-elim (whnfRedTerm d' sucₙ)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (cast-subst d x x₁ x₂) (cast-subst d' x₃ x₄ x₅) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-subst d' x₃ x₄) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Π-subst x₃ x₄ d' x₅ x₆) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Π x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-0 x₃) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-S x₃ x₄) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Ind-subst d' x₃ x₄) = ⊥-elim (whnfRedTerm d Indₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Ind-ctr x₆ x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d Indₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Ind-cong x₃ d′) = ⊥-elim (whnfRedTerm d Indₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-ne-subst y ney d' x₄ x₅) = ⊥-elim (neRedTerm d ney)
whrDetTerm (cast-ne-subst x nex d x₁ x₂) (cast-subst d' x₃ x₄ x₅) = ⊥-elim (neRedTerm d' nex)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-ℕ-subst d' x₃ x₄)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Π-subst x₃ x₄ d' x₅ x₆)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Π x₃ x₄ x₅ x₆ x₇ x₈)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-ℕ-0 x₃)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-ℕ-S x₃ x₄)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Ind-subst d' x₃ x₄)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Ind-ctr x₆ x₃ x₄ x₅)
whrDetTerm (cast-ne-subst x () d x₁ x₂) (cast-Ind-cong x₃ x₄)
whrDetTerm (cast-ne-subst x nex d x₁ x₂) (cast-ne-subst y ney d' x₄ x₅) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-ℕ-subst d x x₁) (cast-subst d' x₂ x₃ x₄) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-subst d' x₂ x₃) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-0 x₂) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-S x₂ x₃) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm {Γ} {u = u} (cast-Ind-subst {i = i} {B = B} {e = e} {t = t} d _ _) d' =
  goCastIndSubst d' PE.refl
  where
  cast-inj : ∀ {l l' A A' B₁ B₂ e₁ e₂ t₁ t₂}
           → cast l A B₁ e₁ t₁ PE.≡ cast l' A' B₂ e₂ t₂
           → l PE.≡ l' × A PE.≡ A' × B₁ PE.≡ B₂ × e₁ PE.≡ e₂ × t₁ PE.≡ t₂
  cast-inj PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl
  goCastIndSubst : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' → s PE.≡ cast ⁰ (Ind i) B e t → u PE.≡ u'
  goCastIndSubst (conv d'' _) eq = goCastIndSubst d'' eq
  goCastIndSubst (cast-Ind-subst d'' _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl =
    PE.cong (λ B′ → cast ⁰ (Ind i) B′ e t) (whrDetTerm d d'')
  goCastIndSubst (cast-subst d'' _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndSubst (cast-Ind-ctr _ _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = ⊥-elim (whnfRedTerm d Indₙ)
  goCastIndSubst (cast-Ind-cong _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = ⊥-elim (whnfRedTerm d Indₙ)
  goCastIndSubst (app-subst _ _ _ _) ()
  goCastIndSubst (β-red _ _ _ _ _ _) ()
  goCastIndSubst (natrec-subst _ _ _ _) ()
  goCastIndSubst (natrec-zero _ _ _) ()
  goCastIndSubst (natrec-suc _ _ _ _) ()
  goCastIndSubst (cast-ne-subst _ neK _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndSubst (cast-ℕ-subst _ _ _) ()
  goCastIndSubst (cast-Π-subst _ _ _ _ _) ()
  goCastIndSubst (cast-Π _ _ _ _ _ _) ()
  goCastIndSubst (cast-ℕ-0 _) ()
  goCastIndSubst (cast-ℕ-S _ _) ()
  goCastIndSubst (cast-ℕ-cong _ _) ()
  goCastIndSubst (cast-ne-cong _ neK _ _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndSubst (IndRect-subst _ _ _ _) ()
  goCastIndSubst (IndRect-ctr _ _ _ _ _ _) ()
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-subst d' x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-Π-subst x₄ x₅ d' x₆ x₇) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) d' = whrDetTerm-aux1 (PE.refl) d'
whrDetTerm (cast-ℕ-0 x) (cast-subst d' x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-0 x₁) = PE.refl
whrDetTerm (cast-ℕ-S x x₁) (cast-subst d' x₂ x₃ x₄) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-S x₂ x₃) = PE.refl
whrDetTerm (cast-ℕ-cong x x₁) (cast-subst d' x₂ x₃ x₄) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-cong x x₁) (cast-ℕ-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-cong x x₁) (cast-ℕ-cong x₂ x₃) rewrite whrDetTerm x₁ x₃ = PE.refl
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-cong x₃ d′) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-cong x₂ d′) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-cong x₁ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-cong x₂ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
whrDetTerm (cast-ℕ-cong x d) (cast-ℕ-0 x₁) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (cast-ℕ-cong x d) (cast-ℕ-S x₁ x₂) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm {Γ} {u = u} (cast-Ind-ctr {ind} {j} {e} {args} _ _ _ _) d' =
  goCastIndCtr d' PE.refl
  where
  cast-inj : ∀ {l l' A A' B B' e₁ e₂ t t'}
           → cast l A B e₁ t PE.≡ cast l' A' B' e₂ t'
           → l PE.≡ l' × A PE.≡ A' × B PE.≡ B' × e₁ PE.≡ e₂ × t PE.≡ t'
  cast-inj PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl
  goCastIndCtr : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' →
                 s PE.≡ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e
                          (ctr (SU.SInd.name ind) j args) → u PE.≡ u'
  goCastIndCtr (conv d'' _) eq = goCastIndCtr d'' eq
  goCastIndCtr (cast-Ind-ctr _ _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , ctr≡ with ctr-PE-injectivity ctr≡
  ... | PE.refl , PE.refl , PE.refl = PE.refl
  goCastIndCtr (cast-subst d'' _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndCtr (cast-Ind-subst d'' _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndCtr (cast-Ind-cong _ d'') eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = ⊥-elim (whnfRedTerm d'' ctrₙ)
  goCastIndCtr (app-subst _ _ _ _) ()
  goCastIndCtr (β-red _ _ _ _ _ _) ()
  goCastIndCtr (natrec-subst _ _ _ _) ()
  goCastIndCtr (natrec-zero _ _ _) ()
  goCastIndCtr (natrec-suc _ _ _ _) ()
  goCastIndCtr (cast-ne-subst _ neK _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndCtr (cast-ℕ-subst _ _ _) ()
  goCastIndCtr (cast-Π-subst _ _ _ _ _) ()
  goCastIndCtr (cast-Π _ _ _ _ _ _) ()
  goCastIndCtr (cast-ℕ-0 _) ()
  goCastIndCtr (cast-ℕ-S _ _) ()
  goCastIndCtr (cast-ℕ-cong _ _) ()
  goCastIndCtr (cast-ne-cong _ neK _ _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndCtr (IndRect-subst _ _ _ _) ()
  goCastIndCtr (IndRect-ctr _ _ _ _ _ _) ()
whrDetTerm {Γ} {u = u} (cast-Ind-cong {i} {e} {t} _ d) d' =
  goCastIndCong d' PE.refl
  where
  cast-inj : ∀ {l l' A A' B B' e₁ e₂ t₁ t₂}
           → cast l A B e₁ t₁ PE.≡ cast l' A' B' e₂ t₂
           → l PE.≡ l' × A PE.≡ A' × B PE.≡ B' × e₁ PE.≡ e₂ × t₁ PE.≡ t₂
  cast-inj PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl
  goCastIndCong : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' → s PE.≡ cast ⁰ (Ind i) (Ind i) e t → u PE.≡ u'
  goCastIndCong (conv d'' _) eq = goCastIndCong d'' eq
  goCastIndCong (cast-Ind-cong _ d'') eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl =
    PE.cong (cast ⁰ (Ind i) (Ind i) e) (whrDetTerm d d'')
  goCastIndCong (cast-subst d'' _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , _ = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndCong (cast-Ind-subst d'' _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = ⊥-elim (whnfRedTerm d'' Indₙ)
  goCastIndCong (cast-Ind-ctr _ _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl = ⊥-elim (whnfRedTerm d ctrₙ)
  goCastIndCong (app-subst _ _ _ _) ()
  goCastIndCong (β-red _ _ _ _ _ _) ()
  goCastIndCong (natrec-subst _ _ _ _) ()
  goCastIndCong (natrec-zero _ _ _) ()
  goCastIndCong (natrec-suc _ _ _ _) ()
  goCastIndCong (cast-ne-subst _ neK _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndCong (cast-ℕ-subst _ _ _) ()
  goCastIndCong (cast-Π-subst _ _ _ _ _) ()
  goCastIndCong (cast-Π _ _ _ _ _ _) ()
  goCastIndCong (cast-ℕ-0 _) ()
  goCastIndCong (cast-ℕ-S _ _) ()
  goCastIndCong (cast-ℕ-cong _ _) ()
  goCastIndCong (cast-ne-cong _ neK _ _ _ _) eq with cast-inj eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl with neK
  ... | ()
  goCastIndCong (IndRect-subst _ _ _ _) ()
  goCastIndCong (IndRect-ctr _ _ _ _ _ _) ()
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-subst X x₁ x₂ x₃) = ⊥-elim (neRedTerm X neK)
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-ne-subst x₁ x₂ X x₃ x₄) = ⊥-elim (neRedTerm X neL)
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-ne-cong x₁ x₂ x₃ x₄ x₅ X) rewrite whrDetTerm d X = PE.refl
whrDetTerm (cast-subst X x x₁ x₂) (cast-ne-cong K neK L neL e tr) = ⊥-elim (neRedTerm X neK)
whrDetTerm (cast-ne-subst x x₁ X x₂ x₃) (cast-ne-cong K neK L neL e tr) = ⊥-elim (neRedTerm X neL)
whrDetTerm (IndRect-subst {ind} {P} {lG} {t} {t'} {ms = ms} _ _ d _) d' =
  whrDetIndRect-subst (SU.SInd.name ind) P lG ms whrDetTerm d d' PE.refl
whrDetTerm {Γ} {u = u} (IndRect-ctr {ind} {j} {P} {lG} {args} {ms = ms} _ _ _ _ _ nth≡) d' =
  go d' PE.refl
  where
  go : ∀ {s u' A' l'} → Γ ⊢ s ⇒ u' ∷ A' ^ l' →
       s PE.≡ IndRect (SU.SInd.name ind) lG P (ctr (SU.SInd.name ind) j args) ms → u PE.≡ u'
  go (conv d'' _) eq = go d'' eq
  go (IndRect-subst _ _ d'' _) eq with IndRect-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , PE.refl , PE.refl =
    ⊥-elim (whnfRedTerm d'' ctrₙ)
  go (IndRect-ctr _ _ _ _ _ nth≡') eq with IndRect-PE-injectivity eq
  ... | PE.refl , PE.refl , PE.refl , ctr≡ , PE.refl with ctr-PE-injectivity ctr≡
  ... | PE.refl , PE.refl , PE.refl
    rewrite just-injective (PE.trans (PE.sym nth≡) nth≡') = PE.refl
  go (app-subst _ _ _ _) ()
  go (β-red _ _ _ _ _ _) ()
  go (natrec-subst _ _ _ _) ()
  go (natrec-zero _ _ _) ()
  go (natrec-suc _ _ _ _) ()
  go (cast-subst _ _ _ _) ()
  go (cast-ne-subst _ _ _ _ _) ()
  go (cast-ℕ-subst _ _ _) ()
  go (cast-Ind-subst _ _ _) ()
  go (cast-Π-subst _ _ _ _ _) ()
  go (cast-Π _ _ _ _ _ _) ()
  go (cast-ℕ-0 _) ()
  go (cast-ℕ-S _ _) ()
  go (cast-ℕ-cong _ _) ()
  go (cast-Ind-ctr _ _ _ _) ()
  go (cast-Ind-cong _ _) ()
  go (cast-ne-cong _ _ _ _ _ _) ()

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
UnotInA[t] () x₁ (ℕⱼ x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () x₁ (Πⱼ _ ▹ _ ▹ x₂ ▹ x₃)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () x₁ (lamⱼ _ _ x₂ x₃)
UnotInA[t] () x₁ (_ ▹ _ ▹ _ ▹ x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ _ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

redU*Term′ : ∀ {A B U′ l Γ r} → U′ PE.≡ (Univ r ¹) → Γ ⊢ A ⇒ U′ ∷ B ^ l → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst _ _ A⇒U x)
redU*Term′ U′≡U (β-red _ _ _ x x₁ x₂) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
redU*Term′ U′≡U (natrec-zero x x₁ x₂) rewrite U′≡U = UnotInA x₁
redU*Term′ () (natrec-suc x x₁ x₂ x₃)
redU*Term′ () (IndRect-subst _ _ _ _)
redU*Term′ {Γ = Γ} {r = r} U′≡U (IndRect-ctr {ind} {j} {args = L.[]} {ms} _ _ _ _ ⊢ms nth≡) =
  look ms _ j ⊢ms nth≡ U′≡U
  where
  look : ∀ ms As n {m} → Γ ⊢All ms ∷ As ^ _ → nth ms n PE.≡ just m → m PE.≡ Univ r ¹ → ⊥
  look L.[] _ n εⱼ ()
  look (_ L.∷ _) _ 0 (consⱼ ⊢m _) PE.refl eq rewrite eq = UnotInA ⊢m
  look (_ L.∷ ms) _ (1+ n) (consⱼ _ ⊢ms) nth≡ eq = look ms _ n ⊢ms nth≡ eq
redU*Term′ U′≡U (IndRect-ctr {ind} {j} {P} {lG} {args = a L.∷ args} {ms} {m} _ _ _ _ _ _) =
  apps-∷≢Univ lG m a
    (args ++ map (λ a′ → IndRect (SU.SInd.name ind) lG P a′ ms) (a L.∷ args)) U′≡U

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

CastRed*Termℕ′ : ∀ {Γ A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ A e t ⇒* cast ⁰ ℕ B e t ∷ A ^ ι ⁰
CastRed*Termℕ′ ⊢e ⊢t  (id (univ ⊢A)) = id (castⱼ (ℕⱼ (wfTerm ⊢A)) ⊢A ⊢e ⊢t)
CastRed*Termℕ′ ⊢e ⊢t  (univ d ⇨ D) = cast-ℕ-subst d ⊢e ⊢t ⇨
                                     conv* (CastRed*Termℕ′
                                             (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (ℕⱼ (wfTerm ⊢e))) (subsetTerm d))) )
                                             ⊢t D)
                                           (sym (subset (univ d)))

CastRed*Termℕ : ∀ {Γ A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ A e t :⇒*: cast ⁰ ℕ B e t ∷ A ^ ι ⁰
CastRed*Termℕ ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (un-univ ⊢A) ⊢e ⊢t ,
     conv (castⱼ (ℕⱼ (wfTerm ⊢e)) (un-univ ⊢B)
          (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (ℕⱼ (wfTerm ⊢e))) (subset*Term (un-univ⇒* D)))))
          ⊢t) (sym (subset* D)) ,
       CastRed*Termℕ′ ⊢e ⊢t D ]]

CastRed*Termℕℕ′ : ∀ {Γ e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ⇒* u ∷ ℕ ^ ι ⁰ )
       → Γ ⊢ cast ⁰ ℕ ℕ e t ⇒* cast ⁰ ℕ ℕ e u ∷ ℕ ^ ι ⁰
CastRed*Termℕℕ′ ⊢e (id ⊢t) = id (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢t)
CastRed*Termℕℕ′ ⊢e (d ⇨ D) = cast-ℕ-cong ⊢e d ⇨ CastRed*Termℕℕ′ ⊢e D

CastRed*Termℕℕ : ∀ {Γ e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t :⇒*: u ∷ ℕ ^ ι ⁰ )
       → Γ ⊢ cast ⁰ ℕ ℕ e t :⇒*: cast ⁰ ℕ ℕ e u ∷ ℕ ^ ι ⁰
CastRed*Termℕℕ ⊢e [[ ⊢t , ⊢u , D ]] =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢t ,
     castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢u ,
       CastRed*Termℕℕ′ ⊢e D ]]

CastRed*Termℕsuc : ∀ {Γ e n}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
         (⊢n : Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ ℕ e (suc n) :⇒*: suc (cast ⁰ ℕ ℕ e n) ∷ ℕ ^ ι ⁰
CastRed*Termℕsuc ⊢e ⊢n =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e (sucⱼ ⊢n) ,
     sucⱼ (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢n) ,
       cast-ℕ-S ⊢e ⊢n ⇨ id (sucⱼ (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢n)) ]]

CastRed*Termℕzero : ∀ {Γ e}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ ℕ e zero :⇒*: zero ∷ ℕ ^ ι ⁰
CastRed*Termℕzero ⊢e =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e (zeroⱼ (wfTerm ⊢e)) ,
     zeroⱼ (wfTerm ⊢e) ,
       cast-ℕ-0 ⊢e ⇨ id (zeroⱼ (wfTerm ⊢e)) ]]

CastRed*TermInd′ : ∀ {Γ i A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind i) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Ind i ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Ind i) A e t ⇒* cast ⁰ (Ind i) B e t ∷ A ^ ι ⁰
CastRed*TermInd′ ⊢e ⊢t  (id (univ ⊢A)) = id (castⱼ (Indⱼ (wfTerm ⊢A)) ⊢A ⊢e ⊢t)
CastRed*TermInd′ {i = i} ⊢e ⊢t  (univ d ⇨ D) = cast-Ind-subst d ⊢e ⊢t ⇨
                                     conv* (CastRed*TermInd′
                                             (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (Indⱼ (wfTerm ⊢e))) (subsetTerm d))) )
                                             ⊢t D)
                                           (sym (subset (univ d)))

CastRed*TermInd : ∀ {Γ i A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind i) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Ind i ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Ind i) A e t :⇒*: cast ⁰ (Ind i) B e t ∷ A ^ ι ⁰
CastRed*TermInd ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] =
  [[ castⱼ (Indⱼ (wfTerm ⊢e)) (un-univ ⊢A) ⊢e ⊢t ,
     conv (castⱼ (Indⱼ (wfTerm ⊢e)) (un-univ ⊢B)
          (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (Indⱼ (wfTerm ⊢e))) (subset*Term (un-univ⇒* D)))))
          ⊢t) (sym (subset* D)) ,
       CastRed*TermInd′ ⊢e ⊢t D ]]

CastRed*TermIndInd′ : ∀ {Γ i e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind i) (Ind i) ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ⇒* u ∷ Ind i ^ ι ⁰ )
       → Γ ⊢ cast ⁰ (Ind i) (Ind i) e t ⇒* cast ⁰ (Ind i) (Ind i) e u ∷ Ind i ^ ι ⁰
CastRed*TermIndInd′ ⊢e (id ⊢t) = id (castⱼ (Indⱼ (wfTerm ⊢e)) (Indⱼ (wfTerm ⊢e)) ⊢e ⊢t)
CastRed*TermIndInd′ ⊢e (d ⇨ D) = cast-Ind-cong ⊢e d ⇨ CastRed*TermIndInd′ ⊢e D

CastRed*TermIndInd : ∀ {Γ i e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind i) (Ind i) ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t :⇒*: u ∷ Ind i ^ ι ⁰ )
       → Γ ⊢ cast ⁰ (Ind i) (Ind i) e t :⇒*: cast ⁰ (Ind i) (Ind i) e u ∷ Ind i ^ ι ⁰
CastRed*TermIndInd ⊢e [[ ⊢t , ⊢u , D ]] =
  [[ castⱼ (Indⱼ (wfTerm ⊢e)) (Indⱼ (wfTerm ⊢e)) ⊢e ⊢t ,
     castⱼ (Indⱼ (wfTerm ⊢e)) (Indⱼ (wfTerm ⊢e)) ⊢e ⊢u ,
       CastRed*TermIndInd′ ⊢e D ]]

CastRed*TermIndctr : ∀ {Γ ind j e args Ts}
         (ind∈ : ind ∈ₗ senv)
         (eq : SU.ctrArgsTypeList ind j PE.≡ just Ts)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ])
         (⊢args : Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e (ctr (SU.SInd.name ind) j args)
           :⇒*: ctr (SU.SInd.name ind) j
                  (map (λ a → cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e a) args)
           ∷ Ind (SU.SInd.name ind) ^ ι ⁰
CastRed*TermIndctr {Γ} {ind} {j} {e} {args} {Ts} ind∈ eq ⊢e ⊢args =
  let ⊢Γ = wfTerm ⊢e
      ⊢castArgs = castAll (all∈ (SU.ctrArgsTypesPositive ind j Ts eq)) ⊢args
      ⊢rhs = Ctrⱼ ⊢Γ ind∈ eq ⊢castArgs
  in [[ castⱼ (Indⱼ ⊢Γ) (Indⱼ ⊢Γ) ⊢e (Ctrⱼ ⊢Γ ind∈ eq ⊢args) ,
       ⊢rhs ,
         cast-Ind-ctr ind∈ eq ⊢e ⊢args ⇨ id ⊢rhs ]]
  where
    i = SU.SInd.name ind

    emb-stype-pos : ∀ (T : SU.Type) → SU.isPositive i T → emb-stype T PE.≡ Ind i
    emb-stype-pos (SU.Ind j′) i≡i = PE.cong Ind (PE.sym i≡i)
    emb-stype-pos (SU.Arrow _ _) ()

    castAll : ∀ {args} {Ts : L.List SU.Type}
            → All (SU.isPositive i) Ts
            → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
            → Γ ⊢All map (λ a → cast ⁰ (Ind i) (Ind i) e a) args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
    castAll []ₐ εⱼ = εⱼ
    castAll (pos ∷ₐ poss) (consⱼ ⊢t ⊢ts) =
      let emb≡Ind = emb-stype-pos _ pos
          ⊢tInd = PE.subst (λ A → _ ⊢ _ ∷ A ^ [ ! , ι ⁰ ]) emb≡Ind ⊢t
          ⊢cast = castⱼ (Indⱼ (wfTerm ⊢e)) (Indⱼ (wfTerm ⊢e)) ⊢e ⊢tInd
          ⊢cast′ = PE.subst (λ A → _ ⊢ cast ⁰ (Ind i) (Ind i) e _ ∷ A ^ [ ! , ι ⁰ ])
                            (PE.sym emb≡Ind) ⊢cast
      in  consⱼ ⊢cast′ (castAll poss ⊢ts)

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
