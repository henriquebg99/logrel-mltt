import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.IndRectCong (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs

open import Definition.Untyped senv
open import Definition.Untyped.Properties senv
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.Weakening senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.IndRect senv swf equivs
  using (ctrArity; branchTy-nf; Πarg; Πih; ihFun; ihGo; ctrVars; concl; minus-<-; varIdx)
open import Tools.Nat
open import Tools.Product
open import Tools.List using (List; All; []ₐ; _∷ₐ_; map; length; length-range; replicate; range; zip; foldr;
                              _∈ₗ_; ∈ₗ-range; all∈; zip-range-nth)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Tools.Maybe using (just)
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU

-- Congruence of the type of the methods in IndRect, under equality of the
-- motive.  The branch types use the motive only through instantiations
-- P [ u ]↑^ d buried in a nested Π-chain, so transporting them along
-- P ≡ P′ is an induction over that chain.  Its leaves need the motive
-- congruence under a substitution, which is a consequence of the fundamental
-- theorem, so it is taken as a hypothesis here: both
-- Definition.LogicalRelation.Fundamental and the modules downstream of it
-- need this induction, and Fundamental cannot import its own consequences
-- (see Definition.Typed.Consequences.IndRectCong for the latter).

-- The motive, instantiated with an argument of type [Ind i] living [d] types
-- further out, is well-formed and congruent.
MotiveCong : Nat → Con Term → Term → Term → Level → Set
MotiveCong i Γ P P′ lG =
  ∀ {Δ u} d → ⊢ Δ → Δ ⊢ˢ wk1^Subst d idSubst ∷ Γ → Δ ⊢ u ∷ Ind i ^ [ ! , ι ⁰ ]
  → Δ ⊢ P [ u ]↑^ d ^ [ ! , ι lG ] × Δ ⊢ P [ u ]↑^ d ≡ P′ [ u ]↑^ d ^ [ ! , ι lG ]

private
  -- [Γ] extended by [m] copies of [Ind i], grown on the left so that it
  -- follows the recursion of the telescopes below.
  ext : Nat → Con Term → Nat → Con Term
  ext i Γ 0 = Γ
  ext i Γ (1+ m) = ext i (Γ ∙ Ind i ^ [ ! , ι ⁰ ]) m

  ext-snoc : ∀ i Γ m → ext i Γ (1+ m) PE.≡ ext i Γ m ∙ Ind i ^ [ ! , ι ⁰ ]
  ext-snoc i Γ 0 = PE.refl
  ext-snoc i Γ (1+ m) = ext-snoc i (Γ ∙ Ind i ^ [ ! , ι ⁰ ]) m

  ⊢ext : ∀ i {Γ} m → ⊢ Γ → ⊢ ext i Γ m
  ⊢ext i 0 ⊢Γ = ⊢Γ
  ⊢ext i (1+ m) ⊢Γ = ⊢ext i m (⊢Γ ∙ univ (Indⱼ ⊢Γ))

  -- Weakening of a well-formed substitution by one type (clone of wk1Subst′,
  -- which lives in a module that imports this one).
  wk1Subst″ : ∀ {F rF σ Γ Δ} → ⊢ Γ → (⊢Δ : ⊢ Δ) → Δ ⊢ F ^ rF → Δ ⊢ˢ σ ∷ Γ
            → (Δ ∙ F ^ rF) ⊢ˢ wk1Subst σ ∷ Γ
  wk1Subst″ ε ⊢Δ ⊢F id = id
  wk1Subst″ (_∙_ {A = A} ⊢Γ ⊢A) ⊢Δ ⊢F ([tailσ] , [headσ]) =
    wk1Subst″ ⊢Γ ⊢Δ ⊢F [tailσ]
    , PE.subst (λ X → _ ⊢ _ ∷ X ^ _) (wk-subst A) (wkTerm (step id) (⊢Δ ∙ ⊢F) [headσ])

  -- The identity substitution is well-formed (clone of idSubst′, which lives in
  -- a module that imports this one).
  idSubst″ : ∀ {Γ} → ⊢ Γ → Γ ⊢ˢ idSubst ∷ Γ
  idSubst″ ε = id
  idSubst″ (_∙_ {Γ} {A} {rA} ⊢Γ ⊢A) =
    wk1Subst″ ⊢Γ ⊢Γ ⊢A (idSubst″ ⊢Γ)
    , PE.subst (λ X → Γ ∙ A ^ rA ⊢ _ ∷ X ^ rA) (wk1-tailId A) (var (⊢Γ ∙ ⊢A) here)

  ext-subst : ∀ i {Γ} m → (⊢Γ : ⊢ Γ) → ext i Γ m ⊢ˢ wk1^Subst m idSubst ∷ Γ
  ext-subst i 0 ⊢Γ = idSubst″ ⊢Γ
  ext-subst i {Γ} (1+ m) ⊢Γ =
    PE.subst (λ Δ → Δ ⊢ˢ wk1Subst (wk1^Subst m idSubst) ∷ Γ) (PE.sym (ext-snoc i Γ m))
             (wk1Subst″ ⊢Γ (⊢ext i m ⊢Γ) (univ (Indⱼ (⊢ext i m ⊢Γ))) (ext-subst i m ⊢Γ))

  ext-var : ∀ i {Γ} m x → x << m → ⊢ Γ → ext i Γ m ⊢ var x ∷ Ind i ^ [ ! , ι ⁰ ]
  ext-var i 0 x () ⊢Γ
  ext-var i {Γ} (1+ m) x h ⊢Γ =
    PE.subst (λ Δ → Δ ⊢ var x ∷ Ind i ^ [ ! , ι ⁰ ]) (PE.sym (ext-snoc i Γ m)) (go x h)
    where
    ⊢Δ∙ = ⊢ext i m ⊢Γ ∙ univ (Indⱼ (⊢ext i m ⊢Γ))

    go : ∀ x → x << 1+ m → ext i Γ m ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ var x ∷ Ind i ^ [ ! , ι ⁰ ]
    go 0 h′ = var ⊢Δ∙ here
    go (1+ x) (leS h′) = wkTerm (step id) ⊢Δ∙ (ext-var i m x h′ ⊢Γ)

  -- The arguments of the constructor, as variables.
  ctrVarsⱼ : ∀ {i Δ} n (Ts : List SU.Type) → All (SU.isPositive i) Ts
           → (∀ v → v << n → Δ ⊢ var (((n + n) - 1) - v) ∷ Ind i ^ [ ! , ι ⁰ ])
           → (vs : List Nat) → All (λ v → v << n) vs → length vs PE.≡ length Ts
           → Δ ⊢All map (λ v → var (((n + n) - 1) - v)) vs ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
  ctrVarsⱼ n []ₗ []ₐ f []ₗ []ₐ eq = εⱼ
  ctrVarsⱼ n []ₗ []ₐ f (_ ∷ₗ _) _ ()
  ctrVarsⱼ n (SU.Arrow _ _ ∷ₗ _) (() ∷ₐ _) f vs hs eq
  ctrVarsⱼ n (SU.Ind _ ∷ₗ Ts) (PE.refl ∷ₐ ps) f (v ∷ₗ vs) (h ∷ₐ hs) eq =
    consⱼ (f v h) (ctrVarsⱼ n Ts ps f vs hs (PE.cong pred eq))
  ctrVarsⱼ n (_ ∷ₗ _) _ f []ₗ []ₐ ()

  -- The telescope of the induction hypotheses.
  teleIh : ∀ {Γ Δ P P′ lG Ss} ind j n ℓ (rs : List Nat)
         → ind ∈ₗ senv
         → SU.ctrArgsTypeList ind j PE.≡ just Ss
         → All (SU.isPositive (SU.SInd.name ind)) Ss
         → n PE.≡ length Ss
         → ℓ + length rs PE.≡ n
         → All (λ r → r << n) rs
         → ⊢ Γ → ⊢ Δ
         → Δ ⊢ˢ wk1^Subst (n + ℓ) idSubst ∷ Γ
         → (∀ x → x << n → Δ ⊢ var (x + ℓ) ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ])
         → MotiveCong (SU.SInd.name ind) Γ P P′ lG
         → Δ ⊢ foldr (Πih ! lG) (concl (SU.SInd.name ind) j P n) (ihGo n P ℓ rs)
             ≡ foldr (Πih ! lG) (concl (SU.SInd.name ind) j P′ n) (ihGo n P′ ℓ rs)
             ∷ Univ ! lG ^ [ ! , next lG ]
  teleIh {Ss = Ss} ind j n ℓ []ₗ ind∈ eqTs pos len eq []ₐ ⊢Γ ⊢Δ [σ] allv motiveCong
    with PE.trans (PE.sym (plusZero ℓ)) eq
  ... | PE.refl =
    un-univ≡ (proj₂ (motiveCong (n + n) ⊢Δ [σ]
                (Ctrⱼ ⊢Δ ind∈ eqTs
                  (ctrVarsⱼ n Ss pos
                    (λ v h → PE.subst (λ y → _ ⊢ var y ∷ _ ^ [ ! , ι ⁰ ])
                                      (PE.trans (plus-comm (((n - 1) - v)) n) (PE.sym (varIdx n v h)))
                                      (allv ((n - 1) - v) (minus-<- n v h)))
                    (range n) (all∈ (∈ₗ-range n)) (PE.trans (length-range n) len)))))
  teleIh {Γ} {Δ} {P} {lG = lG} ind j n ℓ (r ∷ₗ rs) ind∈ eqTs pos len eq (h ∷ₐ hs) ⊢Γ ⊢Δ [σ] allv motiveCong =
    let ⊢ih , ihEq = motiveCong (n + ℓ) ⊢Δ [σ] (allv ((n - 1) - r) (minus-<- n r h))
        ⊢Δ∙ = ⊢Δ ∙ ⊢ih
    in  Π-cong (λ x → (≡is≤ PE.refl) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢ih (un-univ≡ ihEq)
          (teleIh ind j n (1+ ℓ) rs ind∈ eqTs pos len
                  (PE.trans (PE.sym (plusSuc ℓ (length rs))) eq) hs ⊢Γ ⊢Δ∙
                  (PE.subst (λ d → Δ ∙ ihFun n P r ℓ ^ [ ! , ι lG ] ⊢ˢ wk1^Subst d idSubst ∷ Γ)
                            (PE.sym (plusSuc n ℓ))
                            (wk1Subst″ ⊢Γ ⊢Δ ⊢ih [σ]))
                  (λ x hx → PE.subst (λ y → _ ⊢ var y ∷ _ ^ [ ! , ι ⁰ ]) (PE.sym (plusSuc x ℓ))
                                     (wkTerm (step id) ⊢Δ∙ (allv x hx)))
                  motiveCong)

  -- The telescope of the arguments of the constructor.
  teleArg : ∀ {i Γ lG Z Z′} m
          → ⊢ Γ
          → ext i Γ m ⊢ Z ≡ Z′ ∷ Univ ! lG ^ [ ! , next lG ]
          → Γ ⊢ foldr (Πarg ! lG) Z (replicate m (Ind i))
              ≡ foldr (Πarg ! lG) Z′ (replicate m (Ind i)) ∷ Univ ! lG ^ [ ! , next lG ]
  teleArg 0 ⊢Γ eq = eq
  teleArg {lG = lG} (1+ m) ⊢Γ eq =
    Π-cong (λ x → (⁰min lG) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs))
           (univ (Indⱼ ⊢Γ)) (refl (Indⱼ ⊢Γ)) (teleArg m (⊢Γ ∙ univ (Indⱼ ⊢Γ)) eq)

indRectBranchTyCong : ∀ {Γ P P′ lG Ss} ind j
                    → ind ∈ₗ senv
                    → SU.ctrArgsTypeList ind j PE.≡ just Ss
                    → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ≡ P′ ^ [ ! , ι lG ]
                    → MotiveCong (SU.SInd.name ind) Γ P P′ lG
                    → Γ ⊢ indRectBranchTy (SU.SInd.name ind) j Ss P ! lG
                        ≡ indRectBranchTy (SU.SInd.name ind) j Ss P′ ! lG ^ [ ! , ι lG ]
indRectBranchTyCong ind j ind∈ eqTs P≡P′ motiveCong with wfEq P≡P′
indRectBranchTyCong {Γ} {P} {P′} {lG} {Ss} ind j ind∈ eqTs P≡P′ motiveCong | ⊢Γ ∙ ⊢Ind =
  let i = SU.SInd.name ind
      pos = all∈ (SU.ctrArgsTypesPositive ind j Ss eqTs)
      n = ctrArity Ss
  in  PE.subst₂ (λ A B → Γ ⊢ A ≡ B ^ [ ! , ι lG ])
        (PE.sym (branchTy-nf i j Ss P ! lG pos)) (PE.sym (branchTy-nf i j Ss P′ ! lG pos))
        (univ (teleArg n ⊢Γ
          (teleIh ind j n 0 (range n) ind∈ eqTs pos PE.refl (length-range n)
                  (all∈ (∈ₗ-range n)) ⊢Γ (⊢ext i n ⊢Γ)
                  (PE.subst (λ d → ext i Γ n ⊢ˢ wk1^Subst d idSubst ∷ Γ) (PE.sym (plusZero n))
                            (ext-subst i n ⊢Γ))
                  (λ x hx → PE.subst (λ y → ext i Γ n ⊢ var y ∷ Ind i ^ [ ! , ι ⁰ ])
                                     (PE.sym (plusZero x)) (ext-var i n x hx ⊢Γ))
                  motiveCong)))

private
  branchTyListCong : ∀ {Γ P P′ lG ms ms′} ind (js : List (Nat × List SU.Type))
                   → ind ∈ₗ senv
                   → All (λ jTs → SU.ctrArgsTypeList ind (proj₁ jTs) PE.≡ just (proj₂ jTs)) js
                   → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ≡ P′ ^ [ ! , ι lG ]
                   → MotiveCong (SU.SInd.name ind) Γ P P′ lG
                   → Γ ⊢All ms ≡ ms′ ∷ map (λ jTs → indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P ! lG) js ^ [ ! , ι lG ]
                   → Γ ⊢All ms ≡ ms′ ∷ map (λ jTs → indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P′ ! lG) js ^ [ ! , ι lG ]
  branchTyListCong ind []ₗ ind∈ []ₐ P≡P′ motiveCong εⱼ = εⱼ
  branchTyListCong ind (jTs ∷ₗ js) ind∈ (eqTs ∷ₐ eqs) P≡P′ motiveCong (consⱼ ⊢m≡ ⊢ms≡) =
    consⱼ (conv ⊢m≡ (indRectBranchTyCong ind (proj₁ jTs) ind∈ eqTs P≡P′ motiveCong))
          (branchTyListCong ind js ind∈ eqs P≡P′ motiveCong ⊢ms≡)

indRectBranchTyListCong : ∀ {Γ ind P P′ lG ms ms′}
  → ind ∈ₗ senv
  → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ≡ P′ ^ [ ! , ι lG ]
  → MotiveCong (SU.SInd.name ind) Γ P P′ lG
  → Γ ⊢All ms ≡ ms′ ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
  → Γ ⊢All ms ≡ ms′ ∷ indRectBranchTyList ind P′ ! lG ^ [ ! , ι lG ]
indRectBranchTyListCong {ind = ind} ind∈ P≡P′ motiveCong ⊢ms≡ =
  branchTyListCong ind (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) ind∈
                   (all∈ (zip-range-nth (SU.SInd.ctrArgsTypes ind))) P≡P′ motiveCong ⊢ms≡
