open import Definition.Typed.EqualityRelation
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.Ind {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Tools.Nat
open import Tools.Product
open import Tools.List using (All; All₂; []ₐ; _∷ₐ_; map; length; length-map; all∈)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU

------------------------------------------------------------------------
-- Congruence helper for All of inductive term equalities

≅AllInd : ∀ {Γ i args args'}
        → ⊢ Γ
        → All₂ (λ a a' → Γ ⊩Ind a ≡ a' ∷Ind i) args args'
        → All₂ (λ a a' → Γ ⊢ a ≅ a' ∷ Ind i ^ [ ! , ι ⁰ ]) args args'
≅AllInd ⊢Γ []ₐ = []ₐ
≅AllInd {i = i} ⊢Γ (Indₜ₌ k k′ d d′ k≡k′ prop ∷ₐ ps) =
  let indK , indK′ = splitInd prop
  in  ≅ₜ-red (id (univ (Indⱼ ⊢Γ))) (redₜ d) (redₜ d′) Indₙ
             (inductiveWhnf indK) (inductiveWhnf indK′) k≡k′
      ∷ₐ ≅AllInd ⊢Γ ps

------------------------------------------------------------------------
-- Map All of reducible Ind-terms into the inductive All / All₂ views

mapAllInd : ∀ {l Γ i args} {D : Γ ⊩Ind Ind i ^ i}
          → All (λ a → Γ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / Indᵣ D) args
          → All (λ a → Γ ⊩Ind a ∷Ind i) args
mapAllInd {l} {Γ} {i} {D = D} []ₐ = []ₐ
mapAllInd {l} {Γ} {i} {D = D} (p ∷ₐ ps) =
  p ∷ₐ mapAllInd {l} {Γ} {i} {D = D} ps

mapAll₂Ind : ∀ {l Γ i args args'} {D : Γ ⊩Ind Ind i ^ i}
           → All₂ (λ a a' → Γ ⊩⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / Indᵣ D) args args'
           → All₂ (λ a a' → Γ ⊩Ind a ≡ a' ∷Ind i) args args'
mapAll₂Ind {l} {Γ} {i} {D = D} []ₐ = []ₐ
mapAll₂Ind {l} {Γ} {i} {D = D} (p ∷ₐ ps) =
  p ∷ₐ mapAll₂Ind {l} {Γ} {i} {D = D} ps

------------------------------------------------------------------------
-- Reducible constructors (specific Ind derivation)

ctrTerm′ : ∀ {l Γ i j args}
         → ([Ind] : Γ ⊩⟨ l ⟩Ind Ind i ^ i)
         → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
         → All (λ a → Γ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / Ind-intr [Ind]) args
         → Γ ⊩⟨ l ⟩ ctr i j args ∷ Ind i ^ [ ! , ι ⁰ ] / Ind-intr [Ind]
ctrTerm′ {l} {i = i} {j = j} {args = args} (noemb D) ⊢args ps =
  let indArgs = mapAllInd {l = l} {D = D} ps
      ⊢Γ = wf (escape {l = l} (Ind-intr (noemb D)))
      ⊢ctr = Ctrⱼ ⊢Γ ⊢args
      lens = PE.trans (⊢All-length ⊢args) (length-map emb-stype (SU.ctrArgsTypeList i j))
  in  Indₜ (ctr i j args) (idRedTerm:*: ⊢ctr)
           (≅-ctr-cong ⊢Γ lens (≅AllInd ⊢Γ (reflAllInd indArgs)))
           (ctrᵣ indArgs)
  where
    ⊢All-length : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → length ts PE.≡ length As
    ⊢All-length εⱼ = PE.refl
    ⊢All-length (consⱼ _ rest) = PE.cong 1+ (⊢All-length rest)
ctrTerm′ (emb emb< x) ⊢args ps = ctrTerm′ x ⊢args ps
ctrTerm′ (emb ∞< x) ⊢args ps = ctrTerm′ x ⊢args ps

-- Reducible inductive constructors from reducible arguments.
ctrTerm : ∀ {l Γ i j args}
        → ([Ind] : Γ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
        → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
        → All (λ a → Γ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]) args
        → Γ ⊩⟨ l ⟩ ctr i j args ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]
ctrTerm {i = i} [Ind] ⊢args ps =
  let [Ind]′ = Ind-intr (Ind-elim [Ind])
      ps′ = mapAllIrr [Ind] [Ind]′ ps
  in  irrelevanceTerm [Ind]′ [Ind]
                      (ctrTerm′ (Ind-elim [Ind]) ⊢args ps′)
  where
    mapAllIrr : ∀ {l Γ i args}
              → ([A] [B] : Γ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
              → All (λ a → Γ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [A]) args
              → All (λ a → Γ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [B]) args
    mapAllIrr [A] [B] []ₐ = []ₐ
    mapAllIrr [A] [B] (p ∷ₐ ps) =
      irrelevanceTerm [A] [B] p ∷ₐ mapAllIrr [A] [B] ps

------------------------------------------------------------------------
-- Reducible constructor equality

ctrEqTerm′ : ∀ {l Γ i j args args'}
           → ([Ind] : Γ ⊩⟨ l ⟩Ind Ind i ^ i)
           → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
           → Γ ⊢All args' ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
           → All₂ (λ a a' → Γ ⊩⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / Ind-intr [Ind]) args args'
           → Γ ⊩⟨ l ⟩ ctr i j args ≡ ctr i j args' ∷ Ind i ^ [ ! , ι ⁰ ] / Ind-intr [Ind]
ctrEqTerm′ {l} {i = i} {j = j} {args = args} {args' = args'} (noemb D) ⊢args ⊢args' ps =
  let indEq = mapAll₂Ind {l = l} {D = D} ps
      ⊢Γ = wf (escape {l = l} (Ind-intr (noemb D)))
      ⊢ctr  = Ctrⱼ ⊢Γ ⊢args
      ⊢ctr' = Ctrⱼ ⊢Γ ⊢args'
      lens = PE.trans (⊢All-length ⊢args) (length-map emb-stype (SU.ctrArgsTypeList i j))
  in  Indₜ₌ (ctr i j args) (ctr i j args')
            (idRedTerm:*: ⊢ctr) (idRedTerm:*: ⊢ctr')
            (≅-ctr-cong ⊢Γ lens (≅AllInd ⊢Γ indEq))
            (ctrᵣ indEq)
  where
    ⊢All-length : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → length ts PE.≡ length As
    ⊢All-length εⱼ = PE.refl
    ⊢All-length (consⱼ _ rest) = PE.cong 1+ (⊢All-length rest)
ctrEqTerm′ (emb emb< x) ⊢args ⊢args' ps = ctrEqTerm′ x ⊢args ⊢args' ps
ctrEqTerm′ (emb ∞< x) ⊢args ⊢args' ps = ctrEqTerm′ x ⊢args ⊢args' ps

ctrEqTerm : ∀ {l Γ i j args args'}
          → ([Ind] : Γ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
          → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
          → Γ ⊢All args' ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
          → All₂ (λ a a' → Γ ⊩⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]) args args'
          → Γ ⊩⟨ l ⟩ ctr i j args ≡ ctr i j args' ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]
ctrEqTerm {i = i} [Ind] ⊢args ⊢args' ps =
  let [Ind]′ = Ind-intr (Ind-elim [Ind])
      ps′ = mapAll₂Irr [Ind] [Ind]′ ps
  in  irrelevanceEqTerm [Ind]′ [Ind]
                        (ctrEqTerm′ (Ind-elim [Ind]) ⊢args ⊢args' ps′)
  where
    mapAll₂Irr : ∀ {l Γ i args args'}
               → ([A] [B] : Γ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
               → All₂ (λ a a' → Γ ⊩⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / [A]) args args'
               → All₂ (λ a a' → Γ ⊩⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / [B]) args args'
    mapAll₂Irr [A] [B] []ₐ = []ₐ
    mapAll₂Irr [A] [B] (p ∷ₐ ps) =
      irrelevanceEqTerm [A] [B] p ∷ₐ mapAll₂Irr [A] [B] ps

------------------------------------------------------------------------
-- Validity of Ind i

Indᵛ : ∀ {Γ i l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ]
Indᵛ {i = i} [Γ] ⊢Δ [σ] =
  Indᵣ (idRed:*: (univ (Indⱼ ⊢Δ))) , λ _ _ → id (univ (Indⱼ ⊢Δ))

-- Validity of Ind i as a term of U ⁰.
Indᵗᵛ : ∀ {Γ i} ([Γ] : ⊩ᵛ Γ)
     → Γ ⊩ᵛ⟨ ι ¹ ⟩ Ind i ∷ Univ ! ⁰ ^ [ ! , ι ¹ ] / [Γ] / Uᵛ emb< [Γ]
Indᵗᵛ {i = i} [Γ] ⊢Δ [σ] =
  let UIndₜ = Uₜ (Ind i) (idRedTerm:*: (Indⱼ ⊢Δ)) Indₙ (≅ₜ-Indrefl ⊢Δ)
                 (λ _ ⊢Δ₁ → Indᵣ (idRed:*: (univ (Indⱼ ⊢Δ₁))))
  in  UIndₜ , λ _ _ → Uₜ₌ UIndₜ UIndₜ (≅ₜ-Indrefl ⊢Δ)
                            λ _ ⊢Δ₂ → id (univ (Indⱼ ⊢Δ₂))

------------------------------------------------------------------------
-- Apply validity All under a concrete substitution

applyAllᵛ : ∀ {Γ Δ σ i l args}
          → ([Γ] : ⊩ᵛ Γ)
          → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
          → (⊢Δ : ⊢ Δ)
          → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → All (λ a → Γ ⊩ᵛ⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind]) args
          → All (λ a → Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / proj₁ ([Ind] ⊢Δ [σ]))
                (map (subst σ) args)
applyAllᵛ [Γ] [Ind] ⊢Δ [σ] []ₐ = []ₐ
applyAllᵛ [Γ] [Ind] ⊢Δ [σ] ([a] ∷ₐ [as]) =
  proj₁ ([a] ⊢Δ [σ]) ∷ₐ applyAllᵛ [Γ] [Ind] ⊢Δ [σ] [as]

applyAllEqᵛ : ∀ {Γ Δ σ σ′ i l args}
            → ([Γ] : ⊩ᵛ Γ)
            → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
            → (⊢Δ : ⊢ Δ)
            → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
            → ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
            → ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
            → All (λ a → Γ ⊩ᵛ⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind]) args
            → All₂ (λ a a' → Δ ⊩⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / proj₁ ([Ind] ⊢Δ [σ]))
                   (map (subst σ) args) (map (subst σ′) args)
applyAllEqᵛ [Γ] [Ind] ⊢Δ [σ] [σ′] [σ≡σ′] []ₐ = []ₐ
applyAllEqᵛ [Γ] [Ind] ⊢Δ [σ] [σ′] [σ≡σ′] ([a] ∷ₐ [as]) =
  proj₂ ([a] ⊢Δ [σ]) [σ′] [σ≡σ′] ∷ₐ
  applyAllEqᵛ [Γ] [Ind] ⊢Δ [σ] [σ′] [σ≡σ′] [as]

applyAll₂ᵛ : ∀ {Γ Δ σ i l args args'}
           → ([Γ] : ⊩ᵛ Γ)
           → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
           → (⊢Δ : ⊢ Δ)
           → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → All₂ (λ a a' → Γ ⊩ᵛ⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind]) args args'
           → All₂ (λ a a' → Δ ⊩⟨ l ⟩ a ≡ a' ∷ Ind i ^ [ ! , ι ⁰ ] / proj₁ ([Ind] ⊢Δ [σ]))
                  (map (subst σ) args) (map (subst σ) args')
applyAll₂ᵛ [Γ] [Ind] ⊢Δ [σ] []ₐ = []ₐ
applyAll₂ᵛ [Γ] [Ind] ⊢Δ [σ] ([a≡a'] ∷ₐ ps) =
  [a≡a'] ⊢Δ [σ] ∷ₐ applyAll₂ᵛ [Γ] [Ind] ⊢Δ [σ] ps

------------------------------------------------------------------------
-- Validity of constructors

ctrᵛ : ∀ {Γ i j args l}
     → ([Γ] : ⊩ᵛ Γ)
     → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
     → (⊢args : Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ])
     → All (λ a → Γ ⊩ᵛ⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind]) args
     → Γ ⊩ᵛ⟨ l ⟩ ctr i j args ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind]
ctrᵛ {i = i} {j = j} {args = args} {l = l} [Γ] [Ind] ⊢args [args] {σ = σ} ⊢Δ [σ] =
  let [Indσ] = proj₁ ([Ind] ⊢Δ [σ])
      [args]σ = applyAllᵛ [Γ] [Ind] ⊢Δ [σ] [args]
      lens = PE.trans (length-map (subst σ) args)
                     (PE.trans (⊢All-length ⊢args)
                               (length-map emb-stype (SU.ctrArgsTypeList i j)))
      ⊢argsσ = escapeAll [Indσ] ⊢Δ (all∈ (SU.ctrArgsTypesPositive i j)) [args]σ lens
      [ctr] = ctrTerm [Indσ] ⊢argsσ [args]σ
  in  PE.subst (λ t → _ ⊩⟨ _ ⟩ t ∷ Ind i ^ [ ! , ι ⁰ ] / [Indσ])
               (PE.sym (subst-ctr σ i j args))
               [ctr]
    , (λ {σ′} [σ′] [σ≡σ′] →
         let [Indσ′] = proj₁ ([Ind] ⊢Δ [σ′])
             [args]σ′ = applyAllᵛ [Γ] [Ind] ⊢Δ [σ′] [args]
             lens′ = PE.trans (length-map (subst σ′) args)
                              (PE.trans (⊢All-length ⊢args)
                                        (length-map emb-stype (SU.ctrArgsTypeList i j)))
             ⊢argsσ′ = escapeAll [Indσ′] ⊢Δ (all∈ (SU.ctrArgsTypesPositive i j)) [args]σ′ lens′
             [args]≡ = applyAllEqᵛ [Γ] [Ind] ⊢Δ [σ] [σ′] [σ≡σ′] [args]
             [ctr≡] = ctrEqTerm [Indσ] ⊢argsσ ⊢argsσ′ [args]≡
         in  PE.subst₂ (λ t u → _ ⊩⟨ _ ⟩ t ≡ u ∷ Ind i ^ [ ! , ι ⁰ ] / [Indσ])
                       (PE.sym (subst-ctr σ i j args))
                       (PE.sym (subst-ctr σ′ i j args))
                       [ctr≡])
  where
    ⊢All-length : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → length ts PE.≡ length As
    ⊢All-length εⱼ = PE.refl
    ⊢All-length (consⱼ _ rest) = PE.cong 1+ (⊢All-length rest)

    emb-stype-pos : ∀ (T : SU.Type) → SU.isPositive i T → emb-stype T PE.≡ Ind i
    emb-stype-pos (SU.Ind j′) i≡i = PE.cong Ind (PE.sym i≡i)
    emb-stype-pos (SU.Arrow _ _) ()

    escapeAll : ∀ {Δ args Ts}
              → ([Indσ] : Δ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
              → (⊢Δ : ⊢ Δ)
              → All (SU.isPositive i) Ts
              → All (λ a → Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Indσ]) args
              → length args PE.≡ length Ts
              → Δ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
    escapeAll [Indσ] ⊢Δ []ₐ []ₐ _ = εⱼ
    escapeAll {Δ} {args = a ∷ₗ as} {Ts = T ∷ₗ Ts} [Indσ] ⊢Δ (pos ∷ₐ poss) ([a] ∷ₐ ps) eq =
      let emb≡Ind = emb-stype-pos T pos
          ⊢a = escapeTerm [Indσ] [a]
          ⊢Ind≡emb = PE.subst (λ T′ → Δ ⊢ Ind i ≡ T′ ^ [ ! , ι ⁰ ]) (PE.sym emb≡Ind)
                              (refl (univ (Indⱼ ⊢Δ)))
      in  consⱼ (conv ⊢a ⊢Ind≡emb) (escapeAll [Indσ] ⊢Δ poss ps (PE.cong pred eq))
    escapeAll {args = []ₗ} {Ts = _ ∷ₗ _} _ _ _ []ₐ ()
    escapeAll {args = _ ∷ₗ _} {Ts = []ₗ} _ _ []ₐ _ ()
