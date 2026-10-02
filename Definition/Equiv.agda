{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
module Definition.Equiv (senv : SI.SEnv) where
open import Definition.OUntyped senv
open import Definition.OTyped senv
open import Definition.Sort
import Definition.SUntyped as S
import Definition.STyped senv as ST
open import Tools.Nat using (Nat; 1+; _≟_)
open import Tools.Product
open import Tools.Empty using (⊥-elim)
open import Tools.Nullary using (Dec; yes; no)
open import Tools.List using (List; _∈ₗ_; hereₗ; thereₗ)
import Tools.List as TL
import Tools.PropositionalEquality as PE

------------------------------------------------------------------------
-- Types of the components of an equivalence

-- Non-dependent functions between inductive types
Ar : Nat → Nat → Term
Ar i j = Π Ind i ^ ! ° ⁰ ▹ Ind j ° ⁰ ° ⁰ ^ !

-- Π (x : Ind i). Id (Ind i) x (f (g x))
PiId : Nat → Term → Term → Term
PiId i f g =
  Π Ind i ^ ! ° ⁰ ▹ Id (Ind i) (var 0) (f ∘ (g ∘ var 0 ^ ⁰) ^ ⁰) ° ⁰ ° ⁰ ^ %

retrTy : Nat → Term → Term → Term
retrTy B fwd bwd = PiId B fwd bwd

sectTy : Nat → Term → Term → Term
sectTy A fwd bwd = PiId A bwd fwd

------------------------------------------------------------------------
-- An equivalence between two inductive types, as in Rocq's [equiv env].
-- The functions are simple terms; the proofs are observational terms of
-- proof-irrelevant type.  Since there is no weakening for the observational
-- typing, closed proofs are represented as proofs typed in every context.

record Equiv : Set where
  field
    indA : Nat
    indB : Nat
    indA∈ : indA ∈ₗ S.indNames senv
    indB∈ : indB ∈ₗ S.indNames senv
    fwd  : S.Term
    bwd  : S.Term
    retr : Term
    sect : Term

    ⊢fwd  : ∀ {C} → C ST.⊢ fwd ∷ S.Arrow (S.Ind indA) (S.Ind indB)
    ⊢bwd  : ∀ {C} → C ST.⊢ bwd ∷ S.Arrow (S.Ind indB) (S.Ind indA)
    ⊢retr : ∀ {Γ} → ⊢ Γ → Γ ⊢ retr ∷ retrTy indB (emb-sterm-oterm fwd) (emb-sterm-oterm bwd) ^ [ % , ι ⁰ ]
    ⊢sect : ∀ {Γ} → ⊢ Γ → Γ ⊢ sect ∷ sectTy indA (emb-sterm-oterm fwd) (emb-sterm-oterm bwd) ^ [ % , ι ⁰ ]

open Equiv
-- The equivalences between inductive types that the theory is parameterized by
Equivs : Set
Equivs = List Equiv

------------------------------------------------------------------------
-- Embedded simple terms only depend on the variables of their context

private
  wk1-emb-stype-subst : ∀ P σ → subst σ (wk1 (emb-stype-oterm P)) PE.≡ wk1 (emb-stype-oterm P)
  wk1-emb-stype-subst P σ =
    PE.trans (PE.cong (subst σ) (emb-stype-wk-id P (step id)))
      (PE.trans (emb-stype-subst-id P σ) (PE.sym (emb-stype-wk-id P (step id))))

  wk1-emb-stype-wk : ∀ P ρ → wk ρ (wk1 (emb-stype-oterm P)) PE.≡ wk1 (emb-stype-oterm P)
  wk1-emb-stype-wk P ρ =
    PE.trans (PE.cong (wk ρ) (emb-stype-wk-id P (step id)))
      (PE.trans (emb-stype-wk-id P ρ) (PE.sym (emb-stype-wk-id P (step id))))

mutual
  emb-sterm-subst-fix : ∀ {Δ t A σ}
    → (∀ {x B} → x ST.∷ B ∈ Δ → σ x PE.≡ var x)
    → Δ ST.⊢ t ∷ A → subst σ (emb-sterm-oterm t) PE.≡ emb-sterm-oterm t
  emb-sterm-subst-fix fix (ST.varⱼ h) = fix h
  emb-sterm-subst-fix fix (ST.appⱼ ⊢f ⊢a) =
    PE.cong₂ (λ f a → f ∘ a ^ ⁰) (emb-sterm-subst-fix fix ⊢f) (emb-sterm-subst-fix fix ⊢a)
  emb-sterm-subst-fix {σ = σ} fix (ST.lamⱼ {A = A} _ ⊢t) =
    PE.cong₂ (λ A t → lam A ▹ t ^ ⁰) (emb-stype-subst-id A σ) (emb-sterm-subst-fix fix′ ⊢t)
    where
    fix′ : ∀ {x B} → x ST.∷ B ∈ (A ST.∙ _) → liftSubst σ x PE.≡ var x
    fix′ ST.here = PE.refl
    fix′ (ST.there h) = PE.cong wk1 (fix h)
  emb-sterm-subst-fix fix (ST.ctrⱼ _ _ _ ⊢args) =
    PE.cong (gen (Ctrkind _ _)) (emb-sterm-substGen-fix fix ⊢args)
  emb-sterm-subst-fix {σ = σ} fix (ST.indRectⱼ {ind = ind} {P = P} _ _ ⊢t ⊢ms) =
    PE.cong₂ (λ P′ rest → gen (IndRectkind (S.SInd.name ind) ⁰) (⟦ 1 , P′ ⟧ TL.∷ rest))
      (wk1-emb-stype-subst P (liftSubst σ))
      (PE.cong₂ (λ t ms → ⟦ 0 , t ⟧ TL.∷ ms) (emb-sterm-subst-fix fix ⊢t) (emb-sterm-substGen-fix fix ⊢ms))

  emb-sterm-substGen-fix : ∀ {Δ ts As σ}
    → (∀ {x B} → x ST.∷ B ∈ Δ → σ x PE.≡ var x)
    → Δ ST.⊢All ts ∷ As
    → substGen σ (TL.map (λ t → ⟦ 0 , t ⟧) (emb-sterm-oterm-all ts))
      PE.≡ TL.map (λ t → ⟦ 0 , t ⟧) (emb-sterm-oterm-all ts)
  emb-sterm-substGen-fix fix ST.εⱼ = PE.refl
  emb-sterm-substGen-fix fix (ST.consⱼ ⊢t ⊢ts) =
    PE.cong₂ TL._∷_ (PE.cong (λ t → ⟦ 0 , t ⟧) (emb-sterm-subst-fix fix ⊢t))
      (emb-sterm-substGen-fix fix ⊢ts)

mutual
  emb-sterm-wk-fix : ∀ {Δ t A ρ}
    → (∀ {x B} → x ST.∷ B ∈ Δ → wkVar ρ x PE.≡ x)
    → Δ ST.⊢ t ∷ A → wk ρ (emb-sterm-oterm t) PE.≡ emb-sterm-oterm t
  emb-sterm-wk-fix fix (ST.varⱼ h) = PE.cong var (fix h)
  emb-sterm-wk-fix fix (ST.appⱼ ⊢f ⊢a) =
    PE.cong₂ (λ f a → f ∘ a ^ ⁰) (emb-sterm-wk-fix fix ⊢f) (emb-sterm-wk-fix fix ⊢a)
  emb-sterm-wk-fix {ρ = ρ} fix (ST.lamⱼ {A = A} _ ⊢t) =
    PE.cong₂ (λ A t → lam A ▹ t ^ ⁰) (emb-stype-wk-id A ρ) (emb-sterm-wk-fix fix′ ⊢t)
    where
    fix′ : ∀ {x B} → x ST.∷ B ∈ (A ST.∙ _) → wkVar (lift ρ) x PE.≡ x
    fix′ ST.here = PE.refl
    fix′ (ST.there h) = PE.cong 1+ (fix h)
  emb-sterm-wk-fix fix (ST.ctrⱼ _ _ _ ⊢args) =
    PE.cong (gen (Ctrkind _ _)) (emb-sterm-wkGen-fix fix ⊢args)
  emb-sterm-wk-fix {ρ = ρ} fix (ST.indRectⱼ {ind = ind} {P = P} _ _ ⊢t ⊢ms) =
    PE.cong₂ (λ P′ rest → gen (IndRectkind (S.SInd.name ind) ⁰) (⟦ 1 , P′ ⟧ TL.∷ rest))
      (wk1-emb-stype-wk P (lift ρ))
      (PE.cong₂ (λ t ms → ⟦ 0 , t ⟧ TL.∷ ms) (emb-sterm-wk-fix fix ⊢t) (emb-sterm-wkGen-fix fix ⊢ms))

  emb-sterm-wkGen-fix : ∀ {Δ ts As ρ}
    → (∀ {x B} → x ST.∷ B ∈ Δ → wkVar ρ x PE.≡ x)
    → Δ ST.⊢All ts ∷ As
    → wkGen ρ (TL.map (λ t → ⟦ 0 , t ⟧) (emb-sterm-oterm-all ts))
      PE.≡ TL.map (λ t → ⟦ 0 , t ⟧) (emb-sterm-oterm-all ts)
  emb-sterm-wkGen-fix fix ST.εⱼ = PE.refl
  emb-sterm-wkGen-fix fix (ST.consⱼ ⊢t ⊢ts) =
    PE.cong₂ TL._∷_ (PE.cong (λ t → ⟦ 0 , t ⟧) (emb-sterm-wk-fix fix ⊢t))
      (emb-sterm-wkGen-fix fix ⊢ts)

-- Closed simple terms embed to closed terms
emb-closed-subst : ∀ {t A} → TL.[] ST.⊢ t ∷ A → ∀ σ → subst σ (emb-sterm-oterm t) PE.≡ emb-sterm-oterm t
emb-closed-subst ⊢t σ = emb-sterm-subst-fix (λ ()) ⊢t

emb-closed-wk : ∀ {t A} → TL.[] ST.⊢ t ∷ A → ∀ ρ → wk ρ (emb-sterm-oterm t) PE.≡ emb-sterm-oterm t
emb-closed-wk ⊢t ρ = emb-sterm-wk-fix (λ ()) ⊢t

------------------------------------------------------------------------
-- The embedded functions of an equivalence

fwdₒ : Equiv → Term
fwdₒ e = emb-sterm-oterm (fwd e)

bwdₒ : Equiv → Term
bwdₒ e = emb-sterm-oterm (bwd e)

fwdₒ-subst : ∀ e σ → subst σ (fwdₒ e) PE.≡ fwdₒ e
fwdₒ-subst e = emb-closed-subst (⊢fwd e)

bwdₒ-subst : ∀ e σ → subst σ (bwdₒ e) PE.≡ bwdₒ e
bwdₒ-subst e = emb-closed-subst (⊢bwd e)

fwdₒ-wk : ∀ e ρ → wk ρ (fwdₒ e) PE.≡ fwdₒ e
fwdₒ-wk e = emb-closed-wk (⊢fwd e)

bwdₒ-wk : ∀ e ρ → wk ρ (bwdₒ e) PE.≡ bwdₒ e
bwdₒ-wk e = emb-closed-wk (⊢bwd e)

⊢fwdₒ : ∀ e {Γ} → ⊢ Γ → Γ ⊢ fwdₒ e ∷ Ar (indA e) (indB e) ^ [ ! , ι ⁰ ]
⊢fwdₒ e ⊢Γ = emb-sterm-oterm-preserves-typing′ ⊢Γ TL.[]ₐ (⊢fwd e)

⊢bwdₒ : ∀ e {Γ} → ⊢ Γ → Γ ⊢ bwdₒ e ∷ Ar (indB e) (indA e) ^ [ ! , ι ⁰ ]
⊢bwdₒ e ⊢Γ = emb-sterm-oterm-preserves-typing′ ⊢Γ TL.[]ₐ (⊢bwd e)

------------------------------------------------------------------------
-- Typing helpers

-- A closed function between two inductive types
record CFun (i j : Nat) (f : Term) : Set where
  constructor cfun
  field
    ⊢cf      : ∀ {Γ} → ⊢ Γ → Γ ⊢ f ∷ Ar i j ^ [ ! , ι ⁰ ]
    cf-subst : ∀ σ → subst σ f PE.≡ f

open CFun

emb-cfun : ∀ {i j s} → TL.[] ST.⊢ s ∷ S.Arrow (S.Ind i) (S.Ind j) → CFun i j (emb-sterm-oterm s)
emb-cfun ⊢s = cfun (λ ⊢Γ → emb-sterm-oterm-preserves-typing′ ⊢Γ TL.[]ₐ ⊢s) (emb-closed-subst ⊢s)

private
  castTy : ∀ {Γ t A B r} → A PE.≡ B → Γ ⊢ t ∷ A ^ r → Γ ⊢ t ∷ B ^ r
  castTy {Γ} {t} {r = r} eq ⊢t = PE.subst (λ T → Γ ⊢ t ∷ T ^ r) eq ⊢t

  -- A declared inductive type is a type
  Indⱼ′ : ∀ {Γ i} → ⊢ Γ → i ∈ₗ S.indNames senv → Γ ⊢ Ind i ∷ U ⁰ ^ [ ! , ι ¹ ]
  Indⱼ′ ⊢Γ i∈ = emb-stype-oterm-has-type (S.Ind _) i∈ ⊢Γ

  ⊢Ind : ∀ {Γ i} → ⊢ Γ → i ∈ₗ S.indNames senv → Γ ⊢ Ind i ^ [ ! , ι ⁰ ]
  ⊢Ind ⊢Γ i∈ = univ (Indⱼ′ ⊢Γ i∈)

  ⊢∙Ind : ∀ {Γ i} → ⊢ Γ → i ∈ₗ S.indNames senv → ⊢ Γ ∙ Ind i ^ [ ! , ι ⁰ ]
  ⊢∙Ind ⊢Γ i∈ = ⊢Γ ∙ ⊢Ind ⊢Γ i∈

  ⊢var0 : ∀ {Γ i} → ⊢ Γ → i ∈ₗ S.indNames senv → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ var 0 ∷ Ind i ^ [ ! , ι ⁰ ]
  ⊢var0 ⊢Γ i∈ = var (⊢∙Ind ⊢Γ i∈) here

  appⱼ : ∀ {Γ i j f a} → ⊢ Γ → i ∈ₗ S.indNames senv → j ∈ₗ S.indNames senv
    → Γ ⊢ f ∷ Ar i j ^ [ ! , ι ⁰ ]
    → Γ ⊢ a ∷ Ind i ^ [ ! , ι ⁰ ]
    → Γ ⊢ f ∘ a ^ ⁰ ∷ Ind j ^ [ ! , ι ⁰ ]
  appⱼ ⊢Γ i∈ j∈ ⊢f ⊢a = (λ ()) ▹ Indⱼ′ ⊢Γ i∈ ▹ Indⱼ′ (⊢∙Ind ⊢Γ i∈) j∈ ▹ ⊢f ∘ⱼ ⊢a

  lamArⱼ : ∀ {Γ i j t} → ⊢ Γ → i ∈ₗ S.indNames senv
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ t ∷ Ind j ^ [ ! , ι ⁰ ]
    → Γ ⊢ lam Ind i ▹ t ^ ⁰ ∷ Ar i j ^ [ ! , ι ⁰ ]
  lamArⱼ ⊢Γ i∈ ⊢t = lamⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) (λ ()) (⊢Ind ⊢Γ i∈) ⊢t

  lamIdⱼ : ∀ {Γ i t T} → ⊢ Γ → i ∈ₗ S.indNames senv
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ t ∷ T ^ [ % , ι ⁰ ]
    → Γ ⊢ lam Ind i ▹ t ^ ⁰ ∷ Π Ind i ^ ! ° ⁰ ▹ T ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
  lamIdⱼ ⊢Γ i∈ ⊢t = lamⱼ (λ ()) (λ _ → PE.refl , PE.refl) (⊢Ind ⊢Γ i∈) ⊢t

  β-Ind : ∀ {Γ i j t a t′} → ⊢ Γ → i ∈ₗ S.indNames senv
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ t ∷ Ind j ^ [ ! , ι ⁰ ]
    → Γ ⊢ a ∷ Ind i ^ [ ! , ι ⁰ ]
    → t [ a ] PE.≡ t′
    → Γ ⊢ (lam Ind i ▹ t ^ ⁰) ∘ a ^ ⁰ ≡ t′ ∷ Ind j ^ [ ! , ι ⁰ ]
  β-Ind ⊢Γ i∈ ⊢t ⊢a PE.refl = β-red (⁰min ⁰) (⁰min ⁰) (⊢Ind ⊢Γ i∈) ⊢t ⊢a

  -- Substitution under two closed functions
  sub-∘∘ : ∀ {f g} → (∀ σ → subst σ f PE.≡ f) → (∀ σ → subst σ g PE.≡ g)
    → ∀ σ x → subst σ (f ∘ (g ∘ x ^ ⁰) ^ ⁰) PE.≡ f ∘ (g ∘ subst σ x ^ ⁰) ^ ⁰
  sub-∘∘ {f} {g} fs gs σ x = PE.cong₂ (λ f′ g′ → f′ ∘ (g′ ∘ subst σ x ^ ⁰) ^ ⁰) (fs σ) (gs σ)

  -- Γ ∙ Ind i ⊢ Id (Ind i) x (f (g x)) : SProp
  ⊢IdBody : ∀ {Γ i k f g} → ⊢ Γ → i ∈ₗ S.indNames senv → k ∈ₗ S.indNames senv → CFun k i f → CFun i k g
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ Id (Ind i) (var 0) (f ∘ (g ∘ var 0 ^ ⁰) ^ ⁰) ∷ SProp ^ [ ! , next ⁰ ]
  ⊢IdBody ⊢Γ i∈ k∈ cf cg =
    let ⊢Γ′ = ⊢∙Ind ⊢Γ i∈
    in Idⱼ (Indⱼ′ ⊢Γ′ i∈) (⊢var0 ⊢Γ i∈)
           (appⱼ ⊢Γ′ k∈ i∈ (⊢cf cf ⊢Γ′) (appⱼ ⊢Γ′ i∈ k∈ (⊢cf cg ⊢Γ′) (⊢var0 ⊢Γ i∈)))

  -- Instantiating a proof of [PiId i f g] at a point
  appIdⱼ : ∀ {Γ i k f g p a} → ⊢ Γ → i ∈ₗ S.indNames senv → k ∈ₗ S.indNames senv → CFun k i f → CFun i k g
    → Γ ⊢ p ∷ PiId i f g ^ [ % , ι ⁰ ]
    → Γ ⊢ a ∷ Ind i ^ [ ! , ι ⁰ ]
    → Γ ⊢ p ∘ a ^ ⁰ ∷ Id (Ind i) a (f ∘ (g ∘ a ^ ⁰) ^ ⁰) ^ [ % , ι ⁰ ]
  appIdⱼ {i = i} {a = a} ⊢Γ i∈ k∈ cf cg ⊢p ⊢a =
    castTy (PE.cong (Id (Ind i) a) (sub-∘∘ (cf-subst cf) (cf-subst cg) (sgSubst a) (var 0)))
      ((λ _ → PE.refl , PE.refl) ▹ Indⱼ′ ⊢Γ i∈ ▹ ⊢IdBody ⊢Γ i∈ k∈ cf cg ▹ ⊢p ∘ⱼ ⊢a)

------------------------------------------------------------------------
-- Reflexivity

-- λ (x : Ind A). x
idFun : Nat → S.Term
idFun A = S.lam (S.Ind A) (S.var 0)

⊢idFun : ∀ {C} A → A ∈ₗ S.indNames senv → C ST.⊢ idFun A ∷ S.Arrow (S.Ind A) (S.Ind A)
⊢idFun A A∈ = ST.lamⱼ A∈ (ST.varⱼ ST.here)

erefl : (A : Nat) → A ∈ₗ S.indNames senv → Equiv
erefl A A∈ = record
  { indA = A
  ; indB = A
  ; indA∈ = A∈
  ; indB∈ = A∈
  ; fwd  = idFun A
  ; bwd  = idFun A
  ; retr = reflProof
  ; sect = reflProof
  ; ⊢fwd = ⊢idFun A A∈
  ; ⊢bwd = ⊢idFun A A∈
  ; ⊢retr = ⊢reflProof
  ; ⊢sect = ⊢reflProof
  }
  where
  idₒ = emb-sterm-oterm (idFun A)
  reflProof = lam Ind A ▹ Idrefl (Ind A) (var 0) ^ ⁰

  ⊢reflProof : ∀ {Γ} → ⊢ Γ → Γ ⊢ reflProof ∷ PiId A idₒ idₒ ^ [ % , ι ⁰ ]
  ⊢reflProof ⊢Γ =
    let ⊢Γ′ = ⊢∙Ind ⊢Γ A∈
        ⊢x = ⊢var0 ⊢Γ A∈
        ⊢id = lamArⱼ ⊢Γ′ A∈ (⊢var0 ⊢Γ′ A∈)
        -- id (id x) ≡ id x ≡ x
        idid≡ = trans (β-Ind ⊢Γ′ A∈ (⊢var0 ⊢Γ′ A∈) (appⱼ ⊢Γ′ A∈ A∈ ⊢id ⊢x) PE.refl)
                      (β-Ind ⊢Γ′ A∈ (⊢var0 ⊢Γ′ A∈) ⊢x PE.refl)
    in lamIdⱼ ⊢Γ A∈ (conv (Idreflⱼ ⊢x)
                       (univ (Id-cong (refl (Indⱼ′ ⊢Γ′ A∈)) (refl ⊢x) (sym idid≡))))

------------------------------------------------------------------------
-- Composition

-- Given f1 : L → M, g1 : M → L, h : M → Y, k : Y → M,
-- P : Π (m : M). m = f1 (g1 m) and Q : Π (y : Y). y = h (k y),
-- build  λ y. transp (λ z. y = z) (Q y) (ap h (P (k y)))
--   : Π (y : Y). y = (λ x. h (f1 x)) ((λ y. g1 (k y)) y)
-- where [ap h] is itself a transport.  This is the shape of both the
-- retraction and the section of a composite equivalence in Rocq.
compProof : (Y M : Nat) (f1 g1 h k P Q : Term) → Term
compProof Y M f1 g1 h k P Q =
  lam Ind Y ▹
    transp (Ind Y) (Id (Ind Y) (var 1) (var 0))
      (h ∘ (k ∘ var 0 ^ ⁰) ^ ⁰) (Q ∘ var 0 ^ ⁰)
      (h ∘ (f1 ∘ (g1 ∘ (k ∘ var 0 ^ ⁰) ^ ⁰) ^ ⁰) ^ ⁰)
      (transp (Ind M) (Id (Ind Y) (h ∘ (k ∘ var 1 ^ ⁰) ^ ⁰) (h ∘ var 0 ^ ⁰))
        (k ∘ var 0 ^ ⁰) (Idrefl (Ind Y) (h ∘ (k ∘ var 0 ^ ⁰) ^ ⁰))
        (f1 ∘ (g1 ∘ (k ∘ var 0 ^ ⁰) ^ ⁰) ^ ⁰)
        (P ∘ (k ∘ var 0 ^ ⁰) ^ ⁰))
  ^ ⁰

⊢compProof : ∀ {Γ Y M L f1 g1 h k P Q} → ⊢ Γ → Y ∈ₗ S.indNames senv → M ∈ₗ S.indNames senv → L ∈ₗ S.indNames senv
  → CFun L M f1 → CFun M L g1 → CFun M Y h → CFun Y M k
  → (∀ {Δ} → ⊢ Δ → Δ ⊢ P ∷ PiId M f1 g1 ^ [ % , ι ⁰ ])
  → (∀ {Δ} → ⊢ Δ → Δ ⊢ Q ∷ PiId Y h k ^ [ % , ι ⁰ ])
  → Γ ⊢ compProof Y M f1 g1 h k P Q
      ∷ PiId Y (lam Ind L ▹ h ∘ (f1 ∘ var 0 ^ ⁰) ^ ⁰ ^ ⁰)
               (lam Ind Y ▹ g1 ∘ (k ∘ var 0 ^ ⁰) ^ ⁰ ^ ⁰) ^ [ % , ι ⁰ ]
⊢compProof {Γ} {Y} {M} {L} {f1} {g1} {h} {k} {P} {Q} ⊢Γ Y∈ M∈ L∈ cf1 cg1 ch ck ⊢P ⊢Q =
  lamIdⱼ ⊢Γ Y∈ (conv ⊢body (univ (Id-cong (refl (Indⱼ′ ⊢Γ′ Y∈)) (refl ⊢y) (sym HK≡))))
  where
  ⊢Γ′  = ⊢∙Ind ⊢Γ Y∈
  ⊢Γ′′ = ⊢∙Ind ⊢Γ′ M∈
  ⊢y   = ⊢var0 ⊢Γ Y∈
  ky   = k ∘ var 0 ^ ⁰
  u    = f1 ∘ (g1 ∘ ky ^ ⁰) ^ ⁰
  ⊢ky  = appⱼ ⊢Γ′ Y∈ M∈ (⊢cf ck ⊢Γ′) ⊢y
  ⊢gky = appⱼ ⊢Γ′ M∈ L∈ (⊢cf cg1 ⊢Γ′) ⊢ky
  ⊢u   = appⱼ ⊢Γ′ L∈ M∈ (⊢cf cf1 ⊢Γ′) ⊢gky
  ⊢hky = appⱼ ⊢Γ′ M∈ Y∈ (⊢cf ch ⊢Γ′) ⊢ky
  ⊢hu  = appⱼ ⊢Γ′ M∈ Y∈ (⊢cf ch ⊢Γ′) ⊢u

  -- motive of [ap h]: z ↦ h (k y) = h z
  P₁ = Id (Ind Y) (h ∘ (k ∘ var 1 ^ ⁰) ^ ⁰) (h ∘ var 0 ^ ⁰)

  P₁[_] : ∀ t → P₁ [ t ] PE.≡ Id (Ind Y) (h ∘ ky ^ ⁰) (h ∘ t ^ ⁰)
  P₁[ t ] = PE.cong₂ (λ h′ k′ → Id (Ind Y) (h′ ∘ (k′ ∘ var 0 ^ ⁰) ^ ⁰) (h′ ∘ t ^ ⁰))
              (cf-subst ch (sgSubst t)) (cf-subst ck (sgSubst t))

  ⊢P₁ : Γ ∙ Ind Y ^ [ ! , ι ⁰ ] ∙ Ind M ^ [ ! , ι ⁰ ] ⊢ P₁ ^ [ % , ι ⁰ ]
  ⊢P₁ = univ (Idⱼ (Indⱼ′ ⊢Γ′′ Y∈)
                  (appⱼ ⊢Γ′′ M∈ Y∈ (⊢cf ch ⊢Γ′′) (appⱼ ⊢Γ′′ Y∈ M∈ (⊢cf ck ⊢Γ′′) (var ⊢Γ′′ (there here))))
                  (appⱼ ⊢Γ′′ M∈ Y∈ (⊢cf ch ⊢Γ′′) (⊢var0 ⊢Γ′ M∈)))

  -- ap h (P (k y)) : h (k y) = h (f1 (g1 (k y)))
  ⊢ap = castTy P₁[ u ]
          (transpⱼ (⊢Ind ⊢Γ′ M∈) ⊢P₁ ⊢ky (castTy (PE.sym P₁[ ky ]) (Idreflⱼ ⊢hky)) ⊢u
                   (appIdⱼ ⊢Γ′ M∈ L∈ cf1 cg1 (⊢P ⊢Γ′) ⊢ky))

  -- motive of the outer transport: z ↦ y = z
  ⊢P₂ : Γ ∙ Ind Y ^ [ ! , ι ⁰ ] ∙ Ind Y ^ [ ! , ι ⁰ ] ⊢ Id (Ind Y) (var 1) (var 0) ^ [ % , ι ⁰ ]
  ⊢P₂ = univ (Idⱼ (Indⱼ′ (⊢∙Ind ⊢Γ′ Y∈) Y∈) (var (⊢∙Ind ⊢Γ′ Y∈) (there here)) (⊢var0 ⊢Γ′ Y∈))

  -- y = h (f1 (g1 (k y)))
  ⊢body = transpⱼ (⊢Ind ⊢Γ′ Y∈) ⊢P₂ ⊢hky (appIdⱼ ⊢Γ′ Y∈ M∈ ch ck (⊢Q ⊢Γ′) ⊢y) ⊢hu ⊢ap

  -- (λ x. h (f1 x)) ((λ y. g1 (k y)) y) ≡ h (f1 (g1 (k y)))
  ⊢Kλ = lamArⱼ ⊢Γ′ Y∈ (appⱼ (⊢∙Ind ⊢Γ′ Y∈) M∈ L∈ (⊢cf cg1 (⊢∙Ind ⊢Γ′ Y∈))
                     (appⱼ (⊢∙Ind ⊢Γ′ Y∈) Y∈ M∈ (⊢cf ck (⊢∙Ind ⊢Γ′ Y∈)) (⊢var0 ⊢Γ′ Y∈)))
  ⊢Hλ = lamArⱼ ⊢Γ′ L∈ (appⱼ (⊢∙Ind ⊢Γ′ L∈) M∈ Y∈ (⊢cf ch (⊢∙Ind ⊢Γ′ L∈))
                     (appⱼ (⊢∙Ind ⊢Γ′ L∈) L∈ M∈ (⊢cf cf1 (⊢∙Ind ⊢Γ′ L∈)) (⊢var0 ⊢Γ′ L∈)))
  K≡ = β-Ind ⊢Γ′ Y∈ (appⱼ (⊢∙Ind ⊢Γ′ Y∈) M∈ L∈ (⊢cf cg1 (⊢∙Ind ⊢Γ′ Y∈))
                   (appⱼ (⊢∙Ind ⊢Γ′ Y∈) Y∈ M∈ (⊢cf ck (⊢∙Ind ⊢Γ′ Y∈)) (⊢var0 ⊢Γ′ Y∈)))
             ⊢y (sub-∘∘ (cf-subst cg1) (cf-subst ck) (sgSubst (var 0)) (var 0))
  H≡ = β-Ind ⊢Γ′ L∈ (appⱼ (⊢∙Ind ⊢Γ′ L∈) M∈ Y∈ (⊢cf ch (⊢∙Ind ⊢Γ′ L∈))
                   (appⱼ (⊢∙Ind ⊢Γ′ L∈) L∈ M∈ (⊢cf cf1 (⊢∙Ind ⊢Γ′ L∈)) (⊢var0 ⊢Γ′ L∈)))
             ⊢gky (sub-∘∘ (cf-subst ch) (cf-subst cf1) (sgSubst (g1 ∘ ky ^ ⁰)) (var 0))
  HK≡ = trans (app-cong (refl ⊢Hλ) K≡) H≡

-- Composition of two equivalences.  The typing proofs of [e1] are
-- transported along [indB e1 ≡ indA e2].
ecomp : (e1 e2 : Equiv) → indB e1 PE.≡ indA e2 → Equiv
ecomp e1 e2 H = record
  { indA = indA e1
  ; indB = indB e2
  ; indA∈ = indA∈ e1
  ; indB∈ = indB∈ e2
  ; fwd  = S.lam (S.Ind (indA e1)) (S.app (fwd e2) (S.app (fwd e1) (S.var 0)))
  ; bwd  = S.lam (S.Ind (indB e2)) (S.app (bwd e1) (S.app (bwd e2) (S.var 0)))
  ; retr = compProof (indB e2) (indA e2) (fwdₒ e1) (bwdₒ e1) (fwdₒ e2) (bwdₒ e2) (retr e1) (retr e2)
  ; sect = compProof (indA e1) (indA e2) (bwdₒ e2) (fwdₒ e2) (bwdₒ e1) (fwdₒ e1) (sect e2) (sect e1)
  ; ⊢fwd = ST.lamⱼ (indA∈ e1) (ST.appⱼ (⊢fwd e2) (ST.appⱼ ⊢fwd1 (ST.varⱼ ST.here)))
  ; ⊢bwd = ST.lamⱼ (indB∈ e2) (ST.appⱼ ⊢bwd1 (ST.appⱼ (⊢bwd e2) (ST.varⱼ ST.here)))
  ; ⊢retr = λ ⊢Γ → ⊢compProof ⊢Γ (indB∈ e2) (indA∈ e2) (indA∈ e1) (emb-cfun ⊢fwd1) (emb-cfun ⊢bwd1)
                      (emb-cfun (⊢fwd e2)) (emb-cfun (⊢bwd e2)) ⊢retr1 (⊢retr e2)
  ; ⊢sect = λ ⊢Γ → ⊢compProof ⊢Γ (indA∈ e1) (indA∈ e2) (indB∈ e2) (emb-cfun (⊢bwd e2)) (emb-cfun (⊢fwd e2))
                      (emb-cfun ⊢bwd1) (emb-cfun ⊢fwd1) (⊢sect e2) (⊢sect e1)
  }
  where
  ⊢fwd1 : ∀ {C} → C ST.⊢ fwd e1 ∷ S.Arrow (S.Ind (indA e1)) (S.Ind (indA e2))
  ⊢fwd1 {C} = PE.subst (λ m → C ST.⊢ fwd e1 ∷ S.Arrow (S.Ind (indA e1)) (S.Ind m)) H (⊢fwd e1)

  ⊢bwd1 : ∀ {C} → C ST.⊢ bwd e1 ∷ S.Arrow (S.Ind (indA e2)) (S.Ind (indA e1))
  ⊢bwd1 {C} = PE.subst (λ m → C ST.⊢ bwd e1 ∷ S.Arrow (S.Ind m) (S.Ind (indA e1))) H (⊢bwd e1)

  ⊢retr1 : ∀ {Γ} → ⊢ Γ → Γ ⊢ retr e1 ∷ PiId (indA e2) (fwdₒ e1) (bwdₒ e1) ^ [ % , ι ⁰ ]
  ⊢retr1 {Γ} ⊢Γ = PE.subst (λ m → Γ ⊢ retr e1 ∷ PiId m (fwdₒ e1) (bwdₒ e1) ^ [ % , ι ⁰ ]) H (⊢retr e1 ⊢Γ)

------------------------------------------------------------------------
-- Inverse

einv : Equiv → Equiv
einv e = record
  { indA = indB e
  ; indB = indA e
  ; indA∈ = indB∈ e
  ; indB∈ = indA∈ e
  ; fwd  = bwd e
  ; bwd  = fwd e
  ; retr = sect e
  ; sect = retr e
  ; ⊢fwd = ⊢bwd e
  ; ⊢bwd = ⊢fwd e
  ; ⊢retr = ⊢sect e
  ; ⊢sect = ⊢retr e
  }

ecomp-indA : ∀ e1 e2 H → indA (ecomp e1 e2 H) PE.≡ indA e1
ecomp-indA e1 e2 H = PE.refl

ecomp-indB : ∀ e1 e2 H → indB (ecomp e1 e2 H) PE.≡ indB e2
ecomp-indB e1 e2 H = PE.refl

einv-indA : ∀ e → indA (einv e) PE.≡ indB e
einv-indA e = PE.refl

einv-indB : ∀ e → indB (einv e) PE.≡ indA e
einv-indB e = PE.refl

------------------------------------------------------------------------
-- Representatives
--
-- [repr l ind] picks, for the inductive [ind], a representative inductive
-- such that inductives related by an equivalence of [l] get the same
-- representative.  When [ind] is declared, it also gives an equivalence
-- from [ind] to its representative.

Repr : Nat → Set
Repr ind = Σ Nat (λ r → ind ∈ₗ S.indNames senv → Σ Equiv (λ e → indA e PE.≡ ind × indB e PE.≡ r))

rfst : ∀ {ind} → Repr ind → Nat
rfst r = proj₁ r

-- One step of [repr_strong]: [r1], [r2], [r3] are the representatives of
-- [ind], [indA hd] and [indB hd] computed from the tail.
repr-step : ∀ {ind} (hd : Equiv) (r1 : Repr ind) (r2 : Repr (indA hd)) (r3 : Repr (indB hd))
  → Dec (rfst r1 PE.≡ rfst r2) → Repr ind
repr-step hd (i1 , f1) (i2 , f2) (i3 , f3) (yes Heq) =
  i3 , λ ind∈ →
    let e1 , H1a , H1b = f1 ind∈
        e2 , H2a , H2b = f2 (indA∈ hd)
        e3 , H3a , H3b = f3 (indB∈ hd)
    in ecomp e1 (ecomp (einv e2) (ecomp hd e3 (PE.sym H3a)) H2a)
             (PE.trans H1b (PE.trans Heq (PE.sym H2b)))
       , H1a , H3b
repr-step hd r1 r2 r3 (no _) = r1

repr-strong : List Equiv → (ind : Nat) → Repr ind
repr-strong TL.[] ind = ind , λ ind∈ → erefl ind ind∈ , PE.refl , PE.refl
repr-strong (hd TL.∷ tl) ind =
  repr-step hd (repr-strong tl ind) (repr-strong tl (indA hd)) (repr-strong tl (indB hd))
    (rfst (repr-strong tl ind) ≟ rfst (repr-strong tl (indA hd)))

repr : List Equiv → Nat → Nat
repr l ind = rfst (repr-strong l ind)

-- The equivalence from a declared inductive to its representative
repr-eqv : ∀ l ind → ind ∈ₗ S.indNames senv → Equiv
repr-eqv l ind ind∈ = proj₁ (proj₂ (repr-strong l ind) ind∈)

repr-equiv-types : ∀ l ind ind∈ →
  indA (repr-eqv l ind ind∈) PE.≡ ind × indB (repr-eqv l ind ind∈) PE.≡ repr l ind
repr-equiv-types l ind ind∈ = proj₂ (proj₂ (repr-strong l ind) ind∈)

-- If [A] and [B] have the same representative R, then the equivalence A-R
-- has destination R and the equivalence R-B has source R.
repr-equiv-src-dst : ∀ l A B A∈ B∈ → repr l A PE.≡ repr l B
  → indB (repr-eqv l A A∈) PE.≡ indA (einv (repr-eqv l B B∈))
repr-equiv-src-dst l A B A∈ B∈ H =
  PE.trans (proj₂ (repr-equiv-types l A A∈))
           (PE.trans H (PE.sym (proj₂ (repr-equiv-types l B B∈))))

-- The equivalence from [A] to [B] going through their common representative
repr-equiv : ∀ l A B → A ∈ₗ S.indNames senv → B ∈ₗ S.indNames senv → repr l A PE.≡ repr l B → Equiv
repr-equiv l A B A∈ B∈ H =
  ecomp (repr-eqv l A A∈) (einv (repr-eqv l B B∈)) (repr-equiv-src-dst l A B A∈ B∈ H)

repr-equiv-indA : ∀ l A B A∈ B∈ H → indA (repr-equiv l A B A∈ B∈ H) PE.≡ A
repr-equiv-indA l A B A∈ B∈ H = proj₁ (repr-equiv-types l A A∈)

repr-equiv-indB : ∀ l A B A∈ B∈ H → indB (repr-equiv l A B A∈ B∈ H) PE.≡ B
repr-equiv-indB l A B A∈ B∈ H = proj₁ (repr-equiv-types l B B∈)

-- The functions of the equivalence to the representative do not depend on
-- the proof that the inductive is declared
repr-eqv-irr : ∀ l ind p q
  → fwd (repr-eqv l ind p) PE.≡ fwd (repr-eqv l ind q)
  × bwd (repr-eqv l ind p) PE.≡ bwd (repr-eqv l ind q)
repr-eqv-irr TL.[] ind p q = PE.refl , PE.refl
repr-eqv-irr (hd TL.∷ tl) ind p q = go (rfst (repr-strong tl ind) ≟ rfst (repr-strong tl (indA hd)))
  where
  r2 = repr-strong tl (indA hd)
  r3 = repr-strong tl (indB hd)
  go : ∀ d
    → fwd (proj₁ (proj₂ (repr-step hd (repr-strong tl ind) r2 r3 d) p))
      PE.≡ fwd (proj₁ (proj₂ (repr-step hd (repr-strong tl ind) r2 r3 d) q))
    × bwd (proj₁ (proj₂ (repr-step hd (repr-strong tl ind) r2 r3 d) p))
      PE.≡ bwd (proj₁ (proj₂ (repr-step hd (repr-strong tl ind) r2 r3 d) q))
  go (yes Heq) =
    PE.cong₂ (λ X Y → S.lam (S.Ind X) (S.app (fwd mid) (S.app Y (S.var 0))))
      (PE.trans (proj₁ (repr-equiv-types tl ind p)) (PE.sym (proj₁ (repr-equiv-types tl ind q))))
      (proj₁ (repr-eqv-irr tl ind p q))
    , PE.cong (λ Y → S.lam (S.Ind (indB mid)) (S.app Y (S.app (bwd mid) (S.var 0))))
        (proj₂ (repr-eqv-irr tl ind p q))
    where
    e3 = proj₂ r3 (indB∈ hd)
    e2 = proj₂ r2 (indA∈ hd)
    mid = ecomp (einv (proj₁ e2)) (ecomp hd (proj₁ e3) (PE.sym (proj₁ (proj₂ e3)))) (proj₁ (proj₂ e2))
  go (no _) = repr-eqv-irr tl ind p q

repr-equiv-fwd-irr : ∀ l A B A∈ B∈ H A∈′ B∈′ H′
  → fwdₒ (repr-equiv l A B A∈ B∈ H) PE.≡ fwdₒ (repr-equiv l A B A∈′ B∈′ H′)
repr-equiv-fwd-irr l A B A∈ B∈ H A∈′ B∈′ H′ =
  PE.cong emb-sterm-oterm
    (PE.cong₃ (λ X Y Z → S.lam (S.Ind X) (S.app Y (S.app Z (S.var 0))))
      (PE.trans (proj₁ (repr-equiv-types l A A∈)) (PE.sym (proj₁ (repr-equiv-types l A A∈′))))
      (proj₂ (repr-eqv-irr l B B∈ B∈′))
      (proj₁ (repr-eqv-irr l A A∈ A∈′)))

private
  step-yes : ∀ {ind} hd (r1 : Repr ind) r2 r3 p → rfst (repr-step hd r1 r2 r3 (yes p)) PE.≡ rfst r3
  step-yes hd r1 r2 r3 p = PE.refl

  step-no : ∀ {ind} hd (r1 : Repr ind) r2 r3 q → rfst (repr-step hd r1 r2 r3 (no q)) PE.≡ rfst r1
  step-no hd r1 r2 r3 q = PE.refl

  step-self : ∀ hd r2 r3 (d : Dec (rfst r2 PE.≡ rfst r2)) → rfst (repr-step hd r2 r2 r3 d) PE.≡ rfst r3
  step-self hd r2 r3 (yes p) = step-yes hd r2 r2 r3 p
  step-self hd r2 r3 (no q) = ⊥-elim (q PE.refl)

  step-r3 : ∀ hd r2 r3 d → rfst (repr-step hd r3 r2 r3 d) PE.≡ rfst r3
  step-r3 hd r2 r3 (yes p) = step-yes hd r3 r2 r3 p
  step-r3 hd r2 r3 (no q) = PE.refl

  step-cong : ∀ {ind ind′} hd (r1 : Repr ind) (r1′ : Repr ind′) r2 r3
    → rfst r1 PE.≡ rfst r1′ → ∀ d d′
    → rfst (repr-step hd r1 r2 r3 d) PE.≡ rfst (repr-step hd r1′ r2 r3 d′)
  step-cong hd r1 r1′ r2 r3 eq (yes p) (yes p′) =
    PE.trans (step-yes hd r1 r2 r3 p) (PE.sym (step-yes hd r1′ r2 r3 p′))
  step-cong hd r1 r1′ r2 r3 eq (yes p) (no q′) = ⊥-elim (q′ (PE.trans (PE.sym eq) p))
  step-cong hd r1 r1′ r2 r3 eq (no q) (yes p′) = ⊥-elim (q (PE.trans eq p′))
  step-cong hd r1 r1′ r2 r3 eq (no q) (no q′) = eq

-- The two endpoints of an equivalence of [l] have the same representative
repr-same-endpoints : ∀ {l e} → e ∈ₗ l
  → repr l (indA e) PE.≡ repr l (indB e)
repr-same-endpoints {hd TL.∷ tl} hereₗ =
  let rA = repr-strong tl (indA hd)
      rB = repr-strong tl (indB hd)
  in PE.trans (step-self hd rA rB (rfst rA ≟ rfst rA))
              (PE.sym (step-r3 hd rA rB (rfst rB ≟ rfst rA)))
repr-same-endpoints {hd TL.∷ tl} {e} (thereₗ e∈) =
  let rA = repr-strong tl (indA e)
      rB = repr-strong tl (indB e)
      r2 = repr-strong tl (indA hd)
  in step-cong hd rA rB r2 (repr-strong tl (indB hd)) (repr-same-endpoints e∈)
       (rfst rA ≟ rfst r2) (rfst rB ≟ rfst r2)

-- Composable equivalences of [l] have the same representative
transitivity-same-repr : ∀ {l e1 e2} → e1 ∈ₗ l → e2 ∈ₗ l → indB e1 PE.≡ indA e2
  → repr l (indB e2) PE.≡ repr l (indA e1)
transitivity-same-repr {l} e1∈ e2∈ H =
  PE.trans (PE.sym (repr-same-endpoints e2∈))
    (PE.trans (PE.cong (repr l) (PE.sym H))
              (PE.sym (repr-same-endpoints e1∈)))
