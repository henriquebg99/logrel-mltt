import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.IndRectCong (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs

open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.Weakening senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.IndRect senv swf equivs
  using (ctrArity; branchTy-nf; Πarg; Πih; ihFun; ihGo; ctrVars; concl; varIdx; rec-Ind)
open import Tools.Nat
open import Tools.Product
open import Tools.List using (List; All; All₂; []ₐ; _∷ₐ_; map; length; length-range; range; range-suc; zip; foldr;
                              _∈ₗ_; ∈ₗ-map; ∈ₗ-range; all∈; zip-range-nth)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Tools.Maybe using (just)
open import Tools.Inequality using (true; false; filter)
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
  -- The argument types of a constructor are inductive types, by positivity.
  ⊢embT : ∀ {i Δ} T → SU.isPositive i T → SU.indsInSEnv senv T → ⊢ Δ
        → Δ ⊢ emb-stype T ∷ U ⁰ ^ [ ! , ι ¹ ]
  ⊢embT (SU.Ind k) _ k∈ ⊢Δ = Indⱼ′ ⊢Δ k∈
  ⊢embT (SU.Arrow _ _) () _ _

  -- [Γ] extended by the argument types [Ts], grown on the left so that it
  -- follows the recursion of the telescopes below.
  ext : Con Term → List SU.Type → Con Term
  ext Γ []ₗ = Γ
  ext Γ (T ∷ₗ Ts) = ext (Γ ∙ emb-stype T ^ [ ! , ι ⁰ ]) Ts

  ⊢ext : ∀ {i Γ} Ts → All (SU.isPositive i) Ts → All (SU.indsInSEnv senv) Ts
       → ⊢ Γ → ⊢ ext Γ Ts
  ⊢ext []ₗ []ₐ []ₐ ⊢Γ = ⊢Γ
  ⊢ext {i} (T ∷ₗ Ts) (p ∷ₐ ps) (q ∷ₐ qs) ⊢Γ = ⊢ext {i} Ts ps qs (⊢Γ ∙ univ (⊢embT {i} T p q ⊢Γ))

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

  ext-subst : ∀ {i Γ₀ Γ} Ts d → All (SU.isPositive i) Ts → All (SU.indsInSEnv senv) Ts
            → ⊢ Γ₀ → ⊢ Γ → Γ ⊢ˢ wk1^Subst d idSubst ∷ Γ₀
            → ext Γ Ts ⊢ˢ wk1^Subst (length Ts + d) idSubst ∷ Γ₀
  ext-subst []ₗ d []ₐ []ₐ ⊢Γ₀ ⊢Γ [σ] = [σ]
  ext-subst {i} {Γ₀} {Γ} (T ∷ₗ Ts) d (p ∷ₐ ps) (q ∷ₐ qs) ⊢Γ₀ ⊢Γ [σ] =
    let ⊢T = univ (⊢embT {i} T p q ⊢Γ)
    in  PE.subst (λ e → ext (Γ ∙ emb-stype T ^ [ ! , ι ⁰ ]) Ts ⊢ˢ wk1^Subst e idSubst ∷ Γ₀)
                 (plusSuc (length Ts) d)
                 (ext-subst {i} Ts (1+ d) ps qs ⊢Γ₀ (⊢Γ ∙ ⊢T) (wk1Subst″ ⊢Γ₀ ⊢Γ ⊢T [σ]))

  -- A variable of [Γ], seen in the extension.
  ext-wkVar : ∀ {i Γ} Ts x T → All (SU.isPositive i) Ts → All (SU.indsInSEnv senv) Ts → ⊢ Γ
            → Γ ⊢ var x ∷ emb-stype T ^ [ ! , ι ⁰ ]
            → ext Γ Ts ⊢ var (length Ts + x) ∷ emb-stype T ^ [ ! , ι ⁰ ]
  ext-wkVar []ₗ x T []ₐ []ₐ ⊢Γ ⊢x = ⊢x
  ext-wkVar {i} {Γ} (S ∷ₗ Ts) x T (p ∷ₐ ps) (q ∷ₐ qs) ⊢Γ ⊢x =
    let ⊢Γ∙ = ⊢Γ ∙ univ (⊢embT {i} S p q ⊢Γ)
    in  PE.subst (λ y → ext (Γ ∙ emb-stype S ^ [ ! , ι ⁰ ]) Ts ⊢ var y ∷ emb-stype T ^ [ ! , ι ⁰ ])
                 (plusSuc (length Ts) x)
                 (ext-wkVar {i} Ts (1+ x) T ps qs ⊢Γ∙
                    (PE.subst (λ A → Γ ∙ emb-stype S ^ [ ! , ι ⁰ ] ⊢ var (1+ x) ∷ A ^ [ ! , ι ⁰ ]) (wk-emb-stype (step id) T)
                              (wkTerm (step id) ⊢Γ∙ ⊢x)))

  -- The arguments of the constructor, as the variables of the extension.
  ext-vars : ∀ {i Γ} Ts → All (SU.isPositive i) Ts → All (SU.indsInSEnv senv) Ts → ⊢ Γ
           → ext Γ Ts ⊢All map (λ v → var ((length Ts - 1) - v)) (range (length Ts))
                        ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
  ext-vars []ₗ []ₐ []ₐ ⊢Γ = εⱼ
  ext-vars {i} {Γ} (T ∷ₗ Ts) (p ∷ₐ ps) (q ∷ₐ qs) ⊢Γ =
    let m = length Ts
        ⊢Γ∙ = ⊢Γ ∙ univ (⊢embT {i} T p q ⊢Γ)
        Δ = ext (Γ ∙ emb-stype T ^ [ ! , ι ⁰ ]) Ts
    in  PE.subst (λ ts → Δ ⊢All ts ∷ map emb-stype (T ∷ₗ Ts) ^ [ ! , ι ⁰ ])
          (PE.sym (PE.trans (PE.cong (map (λ v → var (m - v))) (range-suc m))
                            (PE.cong (var m ∷ₗ_)
                              (PE.trans (map-map (λ v → var (m - v)) 1+ (range m))
                                        (map-cong (range m) (λ v → PE.cong var (minus-suc m v)))))))
          (consⱼ (PE.subst (λ y → Δ ⊢ var y ∷ emb-stype T ^ [ ! , ι ⁰ ]) (plusZero m)
                   (ext-wkVar {i} Ts 0 T ps qs ⊢Γ∙
                     (PE.subst (λ A → Γ ∙ emb-stype T ^ [ ! , ι ⁰ ] ⊢ var 0 ∷ A ^ [ ! , ι ⁰ ]) (wk-emb-stype (step id) T)
                               (var ⊢Γ∙ here))))
                 (ext-vars {i} Ts ps qs ⊢Γ∙))

  -- Weakening of the arguments by one hypothesis.
  wkArgsⱼ : ∀ {Δ A rA} ℓ n (vs : List Nat) Ss → ⊢ Δ ∙ A ^ rA
          → Δ ⊢All map (λ v → var (((n - 1) - v) + ℓ)) vs ∷ map emb-stype Ss ^ [ ! , ι ⁰ ]
          → Δ ∙ A ^ rA ⊢All map (λ v → var (((n - 1) - v) + 1+ ℓ)) vs
                          ∷ map emb-stype Ss ^ [ ! , ι ⁰ ]
  wkArgsⱼ ℓ n []ₗ []ₗ ⊢Δ∙ εⱼ = εⱼ
  wkArgsⱼ ℓ n []ₗ (S ∷ₗ Ss) ⊢Δ∙ ()
  wkArgsⱼ ℓ n (v ∷ₗ vs) []ₗ ⊢Δ∙ ()
  wkArgsⱼ {Δ} {A} {rA} ℓ n (v ∷ₗ vs) (S ∷ₗ Ss) ⊢Δ∙ (consⱼ ⊢v ⊢vs) =
    consⱼ (PE.subst₂ (λ y B → Δ ∙ A ^ rA ⊢ var y ∷ B ^ [ ! , ι ⁰ ])
                     (PE.sym (plusSuc ((n - 1) - v) ℓ)) (wk-emb-stype (step id) S)
                     (wkTerm (step id) ⊢Δ∙ ⊢v))
          (wkArgsⱼ ℓ n vs Ss ⊢Δ∙ ⊢vs)

  wkRecⱼ : ∀ {Δ A rA i} ℓ n (rs : List Nat) → ⊢ Δ ∙ A ^ rA
         → All (λ r → Δ ⊢ var (((n - 1) - r) + ℓ) ∷ Ind i ^ [ ! , ι ⁰ ]) rs
         → All (λ r → Δ ∙ A ^ rA ⊢ var (((n - 1) - r) + 1+ ℓ) ∷ Ind i ^ [ ! , ι ⁰ ]) rs
  wkRecⱼ ℓ n []ₗ ⊢Δ∙ []ₐ = []ₐ
  wkRecⱼ {Δ} {A} {rA} {i} ℓ n (r ∷ₗ rs) ⊢Δ∙ (⊢r ∷ₐ ⊢rs) =
    PE.subst (λ y → Δ ∙ A ^ rA ⊢ var y ∷ Ind i ^ [ ! , ι ⁰ ]) (PE.sym (plusSuc ((n - 1) - r) ℓ))
             (wkTerm (step id) ⊢Δ∙ ⊢r)
    ∷ₐ wkRecⱼ ℓ n rs ⊢Δ∙ ⊢rs

  -- The recursive arguments are at the inductive type being eliminated.
  recArgsⱼ : ∀ {Δ i} (f : Nat → Term) (vs : List Nat) Ss
           → Δ ⊢All map f vs ∷ map emb-stype Ss ^ [ ! , ι ⁰ ]
           → All (λ r → Δ ⊢ f r ∷ Ind i ^ [ ! , ι ⁰ ])
                 (map proj₁ (filter (λ vS → SU.ctrArgIsRecursive i (proj₂ vS)) (zip vs Ss)))
  recArgsⱼ f []ₗ []ₗ εⱼ = []ₐ
  recArgsⱼ f []ₗ (S ∷ₗ Ss) ()
  recArgsⱼ f (v ∷ₗ vs) []ₗ ()
  recArgsⱼ {i = i} f (v ∷ₗ vs) (S ∷ₗ Ss) (consⱼ ⊢v ⊢vs)
    with SU.ctrArgIsRecursive i S in e
  ... | false = recArgsⱼ f vs Ss ⊢vs
  ... | true with rec-Ind i S e
  ...   | PE.refl = ⊢v ∷ₐ recArgsⱼ f vs Ss ⊢vs

  map-range-cong : ∀ {A : Set} (f g : Nat → A) n → (∀ v → v << n → f v PE.≡ g v)
                 → map f (range n) PE.≡ map g (range n)
  map-range-cong f g 0 eq = PE.refl
  map-range-cong f g (1+ n) eq =
    PE.trans (PE.cong (map f) (range-suc n))
      (PE.trans (PE.cong₂ _∷ₗ_ (eq 0 (leS le0))
                  (PE.trans (map-map f 1+ (range n))
                    (PE.trans (map-range-cong (λ v → f (1+ v)) (λ v → g (1+ v)) n
                                              (λ v h → eq (1+ v) (leS h)))
                              (PE.sym (map-map g 1+ (range n))))))
                (PE.sym (PE.cong (map g) (range-suc n))))

  -- The telescope of the induction hypotheses.
  teleIh : ∀ {Γ Δ P P′ lG} ind j Ts ℓ (rs : List Nat)
         → ind ∈ₗ senv
         → SU.ctrArgsTypeList ind j PE.≡ just Ts
         → ℓ + length rs PE.≡ length (ctrRecIndices (SU.SInd.name ind) Ts)
         → ⊢ Γ → ⊢ Δ
         → Δ ⊢ˢ wk1^Subst (ctrArity Ts + ℓ) idSubst ∷ Γ
         → Δ ⊢All map (λ v → var (((ctrArity Ts - 1) - v) + ℓ)) (range (ctrArity Ts))
                   ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
         → All (λ r → Δ ⊢ var (((ctrArity Ts - 1) - r) + ℓ) ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]) rs
         → MotiveCong (SU.SInd.name ind) Γ P P′ lG
         → Δ ⊢ foldr (Πih ! lG) (concl (SU.SInd.name ind) j P (ctrArity Ts) (length (ctrRecIndices (SU.SInd.name ind) Ts)))
                     (ihGo (ctrArity Ts) P ℓ rs)
             ≡ foldr (Πih ! lG) (concl (SU.SInd.name ind) j P′ (ctrArity Ts) (length (ctrRecIndices (SU.SInd.name ind) Ts)))
                     (ihGo (ctrArity Ts) P′ ℓ rs)
             ∷ Univ ! lG ^ [ ! , next lG ]
  teleIh {Γ} {Δ} ind j Ts ℓ []ₗ ind∈ eqTs eq ⊢Γ ⊢Δ [σ] ⊢args []ₐ motiveCong
    with PE.trans (PE.sym (plusZero ℓ)) eq
  ... | PE.refl =
    let n = ctrArity Ts
    in  un-univ≡ (proj₂ (motiveCong (ℓ + n) ⊢Δ
          (PE.subst (λ d → Δ ⊢ˢ wk1^Subst d idSubst ∷ Γ) (plus-comm n ℓ) [σ])
          (Ctrⱼ ⊢Δ ind∈ eqTs
            (PE.subst (λ ts → Δ ⊢All ts ∷ map emb-stype Ts ^ [ ! , ι ⁰ ])
              (map-range-cong _ _ n
                (λ v h → PE.cong var (PE.trans (plus-comm ((n - 1) - v) ℓ) (PE.sym (varIdx ℓ n v h)))))
              ⊢args))))
  teleIh {Γ} {Δ} {P} {lG = lG} ind j Ts ℓ (r ∷ₗ rs) ind∈ eqTs eq ⊢Γ ⊢Δ [σ] ⊢args (⊢r ∷ₐ ⊢rs) motiveCong =
    let n = ctrArity Ts
        ⊢ih , ihEq = motiveCong (n + ℓ) ⊢Δ [σ] ⊢r
        ⊢Δ∙ = ⊢Δ ∙ ⊢ih
    in  Π-cong (λ x → (≡is≤ PE.refl) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢ih (un-univ≡ ihEq)
          (teleIh ind j Ts (1+ ℓ) rs ind∈ eqTs
                  (PE.trans (PE.sym (plusSuc ℓ (length rs))) eq) ⊢Γ ⊢Δ∙
                  (PE.subst (λ d → Δ ∙ ihFun n P r ℓ ^ [ ! , ι lG ] ⊢ˢ wk1^Subst d idSubst ∷ Γ)
                            (PE.sym (plusSuc n ℓ))
                            (wk1Subst″ ⊢Γ ⊢Δ ⊢ih [σ]))
                  (wkArgsⱼ ℓ n (range n) Ts ⊢Δ∙ ⊢args)
                  (wkRecⱼ ℓ n rs ⊢Δ∙ ⊢rs)
                  motiveCong)

  -- The telescope of the arguments of the constructor.
  teleArg : ∀ {i Γ lG Z Z′} Ts
          → All (SU.isPositive i) Ts → All (SU.indsInSEnv senv) Ts
          → ⊢ Γ
          → ext Γ Ts ⊢ Z ≡ Z′ ∷ Univ ! lG ^ [ ! , next lG ]
          → Γ ⊢ foldr (Πarg ! lG) Z (map emb-stype Ts)
              ≡ foldr (Πarg ! lG) Z′ (map emb-stype Ts) ∷ Univ ! lG ^ [ ! , next lG ]
  teleArg []ₗ []ₐ []ₐ ⊢Γ eq = eq
  teleArg {i} {lG = lG} (T ∷ₗ Ts) (p ∷ₐ ps) (q ∷ₐ qs) ⊢Γ eq =
    let ⊢T = ⊢embT {i} T p q ⊢Γ
    in  Π-cong (λ x → (⁰min lG) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs))
               (univ ⊢T) (refl ⊢T) (teleArg {i} Ts ps qs (⊢Γ ∙ univ ⊢T) eq)

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
      inds = ctrArgInds ind∈ eqTs
      n = ctrArity Ss
      ⊢args = PE.subst (λ ts → ext Γ Ss ⊢All ts ∷ map emb-stype Ss ^ [ ! , ι ⁰ ])
                       (map-cong (range n) (λ v → PE.cong var (PE.sym (plusZero ((n - 1) - v)))))
                       (ext-vars {i} Ss pos inds ⊢Γ)
  in  PE.subst₂ (λ A B → Γ ⊢ A ≡ B ^ [ ! , ι lG ])
        (PE.sym (branchTy-nf i j Ss P ! lG)) (PE.sym (branchTy-nf i j Ss P′ ! lG))
        (univ (teleArg {i} Ss pos inds ⊢Γ
          (teleIh ind j Ss 0 (ctrRecIndices i Ss) ind∈ eqTs PE.refl ⊢Γ (⊢ext {i} Ss pos inds ⊢Γ)
                  (ext-subst {i} Ss 0 pos inds ⊢Γ ⊢Γ (idSubst″ ⊢Γ))
                  ⊢args
                  (recArgsⱼ {i = i} (λ v → var (((n - 1) - v) + 0)) (range n) Ss ⊢args)
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

private
  branchTyListEq : ∀ {Γ P P′ lG} ind (js : List (Nat × List SU.Type))
                 → ind ∈ₗ senv
                 → All (λ jTs → SU.ctrArgsTypeList ind (proj₁ jTs) PE.≡ just (proj₂ jTs)) js
                 → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ≡ P′ ^ [ ! , ι lG ]
                 → MotiveCong (SU.SInd.name ind) Γ P P′ lG
                 → All₂ (λ A A′ → Γ ⊢ A ≡ A′ ^ [ ! , ι lG ])
                        (map (λ jTs → indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P ! lG) js)
                        (map (λ jTs → indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P′ ! lG) js)
  branchTyListEq ind []ₗ ind∈ []ₐ P≡P′ motiveCong = []ₐ
  branchTyListEq ind (jTs ∷ₗ js) ind∈ (eqTs ∷ₐ eqs) P≡P′ motiveCong =
    indRectBranchTyCong ind (proj₁ jTs) ind∈ eqTs P≡P′ motiveCong
    ∷ₐ branchTyListEq ind js ind∈ eqs P≡P′ motiveCong

-- Pointwise equality of the types of the methods, under equality of the motive.
indRectBranchTyListEq : ∀ {Γ ind P P′ lG}
  → ind ∈ₗ senv
  → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ≡ P′ ^ [ ! , ι lG ]
  → MotiveCong (SU.SInd.name ind) Γ P P′ lG
  → All₂ (λ A A′ → Γ ⊢ A ≡ A′ ^ [ ! , ι lG ])
         (indRectBranchTyList ind P ! lG) (indRectBranchTyList ind P′ ! lG)
indRectBranchTyListEq {ind = ind} ind∈ P≡P′ motiveCong =
  branchTyListEq ind (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) ind∈
                 (all∈ (zip-range-nth (SU.SInd.ctrArgsTypes ind))) P≡P′ motiveCong
