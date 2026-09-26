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
    fwd  : S.Term
    bwd  : S.Term
    retr : Term
    sect : Term

    ⊢fwd  : ∀ {C} → C ST.⊢ fwd ∷ S.Arrow (S.Ind indA) (S.Ind indB)
    ⊢bwd  : ∀ {C} → C ST.⊢ bwd ∷ S.Arrow (S.Ind indB) (S.Ind indA)
    ⊢retr : ∀ {Γ} → ⊢ Γ → Γ ⊢ retr ∷ retrTy indB (emb-sterm-oterm fwd) (emb-sterm-oterm bwd) ^ [ % , ι ⁰ ]
    ⊢sect : ∀ {Γ} → ⊢ Γ → Γ ⊢ sect ∷ sectTy indA (emb-sterm-oterm fwd) (emb-sterm-oterm bwd) ^ [ % , ι ⁰ ]

open Equiv
-- FIXME useless definition
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
  emb-sterm-subst-fix {σ = σ} fix (ST.lamⱼ {A = A} ⊢t) =
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
  emb-sterm-wk-fix {ρ = ρ} fix (ST.lamⱼ {A = A} ⊢t) =
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
⊢fwdₒ e ⊢Γ = emb-sterm-oterm-preserves-typing′ ⊢Γ (⊢fwd e)

⊢bwdₒ : ∀ e {Γ} → ⊢ Γ → Γ ⊢ bwdₒ e ∷ Ar (indB e) (indA e) ^ [ ! , ι ⁰ ]
⊢bwdₒ e ⊢Γ = emb-sterm-oterm-preserves-typing′ ⊢Γ (⊢bwd e)

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
emb-cfun ⊢s = cfun (λ ⊢Γ → emb-sterm-oterm-preserves-typing′ ⊢Γ ⊢s) (emb-closed-subst ⊢s)

private
  castTy : ∀ {Γ t A B r} → A PE.≡ B → Γ ⊢ t ∷ A ^ r → Γ ⊢ t ∷ B ^ r
  castTy {Γ} {t} {r = r} eq ⊢t = PE.subst (λ T → Γ ⊢ t ∷ T ^ r) eq ⊢t

  ⊢Ind : ∀ {Γ i} → ⊢ Γ → Γ ⊢ Ind i ^ [ ! , ι ⁰ ]
  ⊢Ind ⊢Γ = univ (Indⱼ ⊢Γ)

  ⊢∙Ind : ∀ {Γ i} → ⊢ Γ → ⊢ Γ ∙ Ind i ^ [ ! , ι ⁰ ]
  ⊢∙Ind ⊢Γ = ⊢Γ ∙ ⊢Ind ⊢Γ

  ⊢var0 : ∀ {Γ i} → ⊢ Γ → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ var 0 ∷ Ind i ^ [ ! , ι ⁰ ]
  ⊢var0 ⊢Γ = var (⊢∙Ind ⊢Γ) here

  appⱼ : ∀ {Γ i j f a} → ⊢ Γ
    → Γ ⊢ f ∷ Ar i j ^ [ ! , ι ⁰ ]
    → Γ ⊢ a ∷ Ind i ^ [ ! , ι ⁰ ]
    → Γ ⊢ f ∘ a ^ ⁰ ∷ Ind j ^ [ ! , ι ⁰ ]
  appⱼ ⊢Γ ⊢f ⊢a = (λ ()) ▹ Indⱼ ⊢Γ ▹ Indⱼ (⊢∙Ind ⊢Γ) ▹ ⊢f ∘ⱼ ⊢a

  lamArⱼ : ∀ {Γ i j t} → ⊢ Γ
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ t ∷ Ind j ^ [ ! , ι ⁰ ]
    → Γ ⊢ lam Ind i ▹ t ^ ⁰ ∷ Ar i j ^ [ ! , ι ⁰ ]
  lamArⱼ ⊢Γ ⊢t = lamⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) (λ ()) (⊢Ind ⊢Γ) ⊢t

  lamIdⱼ : ∀ {Γ i t T} → ⊢ Γ
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ t ∷ T ^ [ % , ι ⁰ ]
    → Γ ⊢ lam Ind i ▹ t ^ ⁰ ∷ Π Ind i ^ ! ° ⁰ ▹ T ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
  lamIdⱼ ⊢Γ ⊢t = lamⱼ (λ ()) (λ _ → PE.refl , PE.refl) (⊢Ind ⊢Γ) ⊢t

  β-Ind : ∀ {Γ i j t a t′} → ⊢ Γ
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ t ∷ Ind j ^ [ ! , ι ⁰ ]
    → Γ ⊢ a ∷ Ind i ^ [ ! , ι ⁰ ]
    → t [ a ] PE.≡ t′
    → Γ ⊢ (lam Ind i ▹ t ^ ⁰) ∘ a ^ ⁰ ≡ t′ ∷ Ind j ^ [ ! , ι ⁰ ]
  β-Ind ⊢Γ ⊢t ⊢a PE.refl = β-red (⁰min ⁰) (⁰min ⁰) (⊢Ind ⊢Γ) ⊢t ⊢a

  -- Substitution under two closed functions
  sub-∘∘ : ∀ {f g} → (∀ σ → subst σ f PE.≡ f) → (∀ σ → subst σ g PE.≡ g)
    → ∀ σ x → subst σ (f ∘ (g ∘ x ^ ⁰) ^ ⁰) PE.≡ f ∘ (g ∘ subst σ x ^ ⁰) ^ ⁰
  sub-∘∘ {f} {g} fs gs σ x = PE.cong₂ (λ f′ g′ → f′ ∘ (g′ ∘ subst σ x ^ ⁰) ^ ⁰) (fs σ) (gs σ)

  -- Γ ∙ Ind i ⊢ Id (Ind i) x (f (g x)) : SProp
  ⊢IdBody : ∀ {Γ i k f g} → ⊢ Γ → CFun k i f → CFun i k g
    → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ Id (Ind i) (var 0) (f ∘ (g ∘ var 0 ^ ⁰) ^ ⁰) ∷ SProp ^ [ ! , next ⁰ ]
  ⊢IdBody ⊢Γ cf cg =
    let ⊢Γ′ = ⊢∙Ind ⊢Γ
    in Idⱼ (Indⱼ ⊢Γ′) (⊢var0 ⊢Γ)
           (appⱼ ⊢Γ′ (⊢cf cf ⊢Γ′) (appⱼ ⊢Γ′ (⊢cf cg ⊢Γ′) (⊢var0 ⊢Γ)))

  -- Instantiating a proof of [PiId i f g] at a point
  appIdⱼ : ∀ {Γ i k f g p a} → ⊢ Γ → CFun k i f → CFun i k g
    → Γ ⊢ p ∷ PiId i f g ^ [ % , ι ⁰ ]
    → Γ ⊢ a ∷ Ind i ^ [ ! , ι ⁰ ]
    → Γ ⊢ p ∘ a ^ ⁰ ∷ Id (Ind i) a (f ∘ (g ∘ a ^ ⁰) ^ ⁰) ^ [ % , ι ⁰ ]
  appIdⱼ {i = i} {a = a} ⊢Γ cf cg ⊢p ⊢a =
    castTy (PE.cong (Id (Ind i) a) (sub-∘∘ (cf-subst cf) (cf-subst cg) (sgSubst a) (var 0)))
      ((λ _ → PE.refl , PE.refl) ▹ Indⱼ ⊢Γ ▹ ⊢IdBody ⊢Γ cf cg ▹ ⊢p ∘ⱼ ⊢a)

------------------------------------------------------------------------
-- Reflexivity

-- λ (x : Ind A). x
idFun : Nat → S.Term
idFun A = S.lam (S.Ind A) (S.var 0)

⊢idFun : ∀ {C} A → C ST.⊢ idFun A ∷ S.Arrow (S.Ind A) (S.Ind A)
⊢idFun A = ST.lamⱼ (ST.varⱼ ST.here)

erefl : Nat → Equiv
erefl A = record
  { indA = A
  ; indB = A
  ; fwd  = idFun A
  ; bwd  = idFun A
  ; retr = reflProof
  ; sect = reflProof
  ; ⊢fwd = ⊢idFun A
  ; ⊢bwd = ⊢idFun A
  ; ⊢retr = ⊢reflProof
  ; ⊢sect = ⊢reflProof
  }
  where
  idₒ = emb-sterm-oterm (idFun A)
  reflProof = lam Ind A ▹ Idrefl (Ind A) (var 0) ^ ⁰

  ⊢reflProof : ∀ {Γ} → ⊢ Γ → Γ ⊢ reflProof ∷ PiId A idₒ idₒ ^ [ % , ι ⁰ ]
  ⊢reflProof ⊢Γ =
    let ⊢Γ′ = ⊢∙Ind ⊢Γ
        ⊢x = ⊢var0 ⊢Γ
        ⊢id = lamArⱼ ⊢Γ′ (⊢var0 ⊢Γ′)
        -- id (id x) ≡ id x ≡ x
        idid≡ = trans (β-Ind ⊢Γ′ (⊢var0 ⊢Γ′) (appⱼ ⊢Γ′ ⊢id ⊢x) PE.refl)
                      (β-Ind ⊢Γ′ (⊢var0 ⊢Γ′) ⊢x PE.refl)
    in lamIdⱼ ⊢Γ (conv (Idreflⱼ ⊢x)
                       (univ (Id-cong (refl (Indⱼ ⊢Γ′)) (refl ⊢x) (sym idid≡))))

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

⊢compProof : ∀ {Γ Y M L f1 g1 h k P Q} → ⊢ Γ
  → CFun L M f1 → CFun M L g1 → CFun M Y h → CFun Y M k
  → (∀ {Δ} → ⊢ Δ → Δ ⊢ P ∷ PiId M f1 g1 ^ [ % , ι ⁰ ])
  → (∀ {Δ} → ⊢ Δ → Δ ⊢ Q ∷ PiId Y h k ^ [ % , ι ⁰ ])
  → Γ ⊢ compProof Y M f1 g1 h k P Q
      ∷ PiId Y (lam Ind L ▹ h ∘ (f1 ∘ var 0 ^ ⁰) ^ ⁰ ^ ⁰)
               (lam Ind Y ▹ g1 ∘ (k ∘ var 0 ^ ⁰) ^ ⁰ ^ ⁰) ^ [ % , ι ⁰ ]
⊢compProof {Γ} {Y} {M} {L} {f1} {g1} {h} {k} {P} {Q} ⊢Γ cf1 cg1 ch ck ⊢P ⊢Q =
  lamIdⱼ ⊢Γ (conv ⊢body (univ (Id-cong (refl (Indⱼ ⊢Γ′)) (refl ⊢y) (sym HK≡))))
  where
  ⊢Γ′  = ⊢∙Ind {i = Y} ⊢Γ
  ⊢Γ′′ = ⊢∙Ind {i = M} ⊢Γ′
  ⊢y   = ⊢var0 {i = Y} ⊢Γ
  ky   = k ∘ var 0 ^ ⁰
  u    = f1 ∘ (g1 ∘ ky ^ ⁰) ^ ⁰
  ⊢ky  = appⱼ ⊢Γ′ (⊢cf ck ⊢Γ′) ⊢y
  ⊢gky = appⱼ ⊢Γ′ (⊢cf cg1 ⊢Γ′) ⊢ky
  ⊢u   = appⱼ ⊢Γ′ (⊢cf cf1 ⊢Γ′) ⊢gky
  ⊢hky = appⱼ ⊢Γ′ (⊢cf ch ⊢Γ′) ⊢ky
  ⊢hu  = appⱼ ⊢Γ′ (⊢cf ch ⊢Γ′) ⊢u

  -- motive of [ap h]: z ↦ h (k y) = h z
  P₁ = Id (Ind Y) (h ∘ (k ∘ var 1 ^ ⁰) ^ ⁰) (h ∘ var 0 ^ ⁰)

  P₁[_] : ∀ t → P₁ [ t ] PE.≡ Id (Ind Y) (h ∘ ky ^ ⁰) (h ∘ t ^ ⁰)
  P₁[ t ] = PE.cong₂ (λ h′ k′ → Id (Ind Y) (h′ ∘ (k′ ∘ var 0 ^ ⁰) ^ ⁰) (h′ ∘ t ^ ⁰))
              (cf-subst ch (sgSubst t)) (cf-subst ck (sgSubst t))

  ⊢P₁ : Γ ∙ Ind Y ^ [ ! , ι ⁰ ] ∙ Ind M ^ [ ! , ι ⁰ ] ⊢ P₁ ^ [ % , ι ⁰ ]
  ⊢P₁ = univ (Idⱼ (Indⱼ ⊢Γ′′)
                  (appⱼ ⊢Γ′′ (⊢cf ch ⊢Γ′′) (appⱼ ⊢Γ′′ (⊢cf ck ⊢Γ′′) (var ⊢Γ′′ (there here))))
                  (appⱼ ⊢Γ′′ (⊢cf ch ⊢Γ′′) (⊢var0 ⊢Γ′)))

  -- ap h (P (k y)) : h (k y) = h (f1 (g1 (k y)))
  ⊢ap = castTy P₁[ u ]
          (transpⱼ (⊢Ind ⊢Γ′) ⊢P₁ ⊢ky (castTy (PE.sym P₁[ ky ]) (Idreflⱼ ⊢hky)) ⊢u
                   (appIdⱼ ⊢Γ′ cf1 cg1 (⊢P ⊢Γ′) ⊢ky))

  -- motive of the outer transport: z ↦ y = z
  ⊢P₂ : Γ ∙ Ind Y ^ [ ! , ι ⁰ ] ∙ Ind Y ^ [ ! , ι ⁰ ] ⊢ Id (Ind Y) (var 1) (var 0) ^ [ % , ι ⁰ ]
  ⊢P₂ = univ (Idⱼ (Indⱼ (⊢∙Ind ⊢Γ′)) (var (⊢∙Ind ⊢Γ′) (there here)) (⊢var0 ⊢Γ′))

  -- y = h (f1 (g1 (k y)))
  ⊢body = transpⱼ (⊢Ind ⊢Γ′) ⊢P₂ ⊢hky (appIdⱼ ⊢Γ′ ch ck (⊢Q ⊢Γ′) ⊢y) ⊢hu ⊢ap

  -- (λ x. h (f1 x)) ((λ y. g1 (k y)) y) ≡ h (f1 (g1 (k y)))
  ⊢Kλ = lamArⱼ ⊢Γ′ (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf cg1 (⊢∙Ind ⊢Γ′))
                     (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf ck (⊢∙Ind ⊢Γ′)) (⊢var0 ⊢Γ′)))
  ⊢Hλ = lamArⱼ ⊢Γ′ (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf ch (⊢∙Ind ⊢Γ′))
                     (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf cf1 (⊢∙Ind ⊢Γ′)) (⊢var0 ⊢Γ′)))
  K≡ = β-Ind ⊢Γ′ (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf cg1 (⊢∙Ind ⊢Γ′))
                   (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf ck (⊢∙Ind ⊢Γ′)) (⊢var0 ⊢Γ′)))
             ⊢y (sub-∘∘ (cf-subst cg1) (cf-subst ck) (sgSubst (var 0)) (var 0))
  H≡ = β-Ind ⊢Γ′ (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf ch (⊢∙Ind ⊢Γ′))
                   (appⱼ (⊢∙Ind ⊢Γ′) (⊢cf cf1 (⊢∙Ind ⊢Γ′)) (⊢var0 ⊢Γ′)))
             ⊢gky (sub-∘∘ (cf-subst ch) (cf-subst cf1) (sgSubst (g1 ∘ ky ^ ⁰)) (var 0))
  HK≡ = trans (app-cong (refl ⊢Hλ) K≡) H≡

-- Composition of two equivalences.  The typing proofs of [e1] are
-- transported along [indB e1 ≡ indA e2].
ecomp : (e1 e2 : Equiv) → indB e1 PE.≡ indA e2 → Equiv
ecomp e1 e2 H = record
  { indA = indA e1
  ; indB = indB e2
  ; fwd  = S.lam (S.Ind (indA e1)) (S.app (fwd e2) (S.app (fwd e1) (S.var 0)))
  ; bwd  = S.lam (S.Ind (indB e2)) (S.app (bwd e1) (S.app (bwd e2) (S.var 0)))
  ; retr = compProof (indB e2) (indA e2) (fwdₒ e1) (bwdₒ e1) (fwdₒ e2) (bwdₒ e2) (retr e1) (retr e2)
  ; sect = compProof (indA e1) (indA e2) (bwdₒ e2) (fwdₒ e2) (bwdₒ e1) (fwdₒ e1) (sect e2) (sect e1)
  ; ⊢fwd = ST.lamⱼ (ST.appⱼ (⊢fwd e2) (ST.appⱼ ⊢fwd1 (ST.varⱼ ST.here)))
  ; ⊢bwd = ST.lamⱼ (ST.appⱼ ⊢bwd1 (ST.appⱼ (⊢bwd e2) (ST.varⱼ ST.here)))
  ; ⊢retr = λ ⊢Γ → ⊢compProof ⊢Γ (emb-cfun ⊢fwd1) (emb-cfun ⊢bwd1)
                      (emb-cfun (⊢fwd e2)) (emb-cfun (⊢bwd e2)) ⊢retr1 (⊢retr e2)
  ; ⊢sect = λ ⊢Γ → ⊢compProof ⊢Γ (emb-cfun (⊢bwd e2)) (emb-cfun (⊢fwd e2))
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
-- together with an equivalence from [ind] to it, such that inductives related
-- by an equivalence of [l] get the same representative.

Repr : Nat → Set
Repr ind = Σ (Nat × Equiv) (λ x → indA (proj₂ x) PE.≡ ind × indB (proj₂ x) PE.≡ proj₁ x)

rfst : ∀ {ind} → Repr ind → Nat
rfst r = proj₁ (proj₁ r)

-- One step of [repr_strong]: [r1], [r2], [r3] are the representatives of
-- [ind], [indA hd] and [indB hd] computed from the tail.
repr-step : ∀ {ind} (hd : Equiv) (r1 : Repr ind) (r2 : Repr (indA hd)) (r3 : Repr (indB hd))
  → Dec (rfst r1 PE.≡ rfst r2) → Repr ind
repr-step hd ((i1 , e1) , H1a , H1b) ((i2 , e2) , H2a , H2b) ((i3 , e3) , H3a , H3b) (yes Heq) =
  (indB e3 , ecomp e1 (ecomp (einv e2) (ecomp hd e3 (PE.sym H3a)) H2a)
                   (PE.trans H1b (PE.trans Heq (PE.sym H2b))))
  , H1a , PE.refl
repr-step hd r1 r2 r3 (no _) = r1

repr-strong : List Equiv → (ind : Nat) → Repr ind
repr-strong TL.[] ind = (ind , erefl ind) , PE.refl , PE.refl
repr-strong (hd TL.∷ tl) ind =
  repr-step hd (repr-strong tl ind) (repr-strong tl (indA hd)) (repr-strong tl (indB hd))
    (rfst (repr-strong tl ind) ≟ rfst (repr-strong tl (indA hd)))

repr : List Equiv → Nat → Nat × Equiv
repr l ind = proj₁ (repr-strong l ind)

repr-equiv-types : ∀ l ind →
  indA (proj₂ (repr l ind)) PE.≡ ind × indB (proj₂ (repr l ind)) PE.≡ proj₁ (repr l ind)
repr-equiv-types l ind = proj₂ (repr-strong l ind)

-- If [A] and [B] have the same representative R, then the equivalence A-R
-- has destination R and the equivalence R-B has source R.
repr-equiv-src-dst : ∀ l A B → proj₁ (repr l A) PE.≡ proj₁ (repr l B)
  → indB (proj₂ (repr l A)) PE.≡ indA (einv (proj₂ (repr l B)))
repr-equiv-src-dst l A B H =
  PE.trans (proj₂ (repr-equiv-types l A))
           (PE.trans H (PE.sym (proj₂ (repr-equiv-types l B))))

-- The equivalence from [A] to [B] going through their common representative
repr-equiv : ∀ l A B → proj₁ (repr l A) PE.≡ proj₁ (repr l B) → Equiv
repr-equiv l A B H =
  ecomp (proj₂ (repr l A)) (einv (proj₂ (repr l B))) (repr-equiv-src-dst l A B H)

repr-equiv-indA : ∀ l A B H → indA (repr-equiv l A B H) PE.≡ A
repr-equiv-indA l A B H = proj₁ (repr-equiv-types l A)

repr-equiv-indB : ∀ l A B H → indB (repr-equiv l A B H) PE.≡ B
repr-equiv-indB l A B H = proj₁ (repr-equiv-types l B)

private
  step-yes : ∀ {ind} hd (r1 : Repr ind) r2 r3 p → rfst (repr-step hd r1 r2 r3 (yes p)) PE.≡ rfst r3
  step-yes hd r1 r2 r3 p = proj₂ (proj₂ r3)

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
  → proj₁ (repr l (indA e)) PE.≡ proj₁ (repr l (indB e))
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
  → proj₁ (repr l (indB e2)) PE.≡ proj₁ (repr l (indA e1))
transitivity-same-repr {l} e1∈ e2∈ H =
  PE.trans (PE.sym (repr-same-endpoints e2∈))
    (PE.trans (PE.cong (λ i → proj₁ (repr l i)) (PE.sym H))
              (PE.sym (repr-same-endpoints e1∈)))
