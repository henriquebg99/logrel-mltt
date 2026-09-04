open import Definition.Typed.EqualityRelation
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.IndRect {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Escape
open import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.Ind
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Nullary using (Dec; yes; no)
open import Tools.List using (All; All₂; []ₐ; _∷ₐ_; map; _++_; lookupDefault; length; length-map; All₂-length; lookupAll₂; all∈; length-range) renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU

------------------------------------------------------------------------
-- Closure of IndRect-subst (clone of natrec2-subst*)

IndRect-subst* : ∀ {Γ i P lG t t′ ms l}
               → Γ ⊢ P ∷ Π Ind i ^ ! ° ⁰ ▹ Univ ! lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ]
               → Γ ⊢ t ⇒* t′ ∷ Ind i ^ ι ⁰
               → Γ ⊢All ms ∷ indRectBranchTyList i P ! lG ^ [ ! , ι lG ]
               → ([Ind] : Γ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
               → Γ ⊩⟨ l ⟩ t′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]
               → (∀ {u u′} → Γ ⊩⟨ l ⟩ u ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]
                           → Γ ⊩⟨ l ⟩ u′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]
                           → Γ ⊩⟨ l ⟩ u ≡ u′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]
                           → Γ ⊢ P ∘ u ^ ¹ ≡ P ∘ u′ ^ ¹ ^ [ ! , ι lG ])
               → Γ ⊢ IndRect i lG P t ms ⇒* IndRect i lG P t′ ms ∷ (P ∘ t ^ ¹) ^ ι lG
IndRect-subst* ⊢P (id ⊢t) ⊢ms [Ind] [t′] prop = id (IndRectⱼ (λ ()) ⊢P ⊢t ⊢ms)
IndRect-subst* ⊢P (x ⇨ t⇒t′) ⊢ms [Ind] [t′] prop =
  let q , w = redSubst*Term t⇒t′ [Ind] [t′]
      a , s = redSubstTerm x [Ind] q
  in  IndRect-subst ⊢P x ⊢ms
      ⇨ conv* (IndRect-subst* ⊢P t⇒t′ ⊢ms [Ind] [t′] prop)
              (prop q a (symEqTerm [Ind] s))

------------------------------------------------------------------------
-- Result type P ∘ t ^ ¹ of IndRect (univ of the application).
-- Counterpart of Fundamental's substS {F = ℕ} {G} {t = n} for natrec:
-- IndRect's motive is a Π-term into Univ, so apply then univ.
-- Unfolded under ⊢Δ [σ] to avoid decompΠᵛ metas on closed Univ.

P∘tᵛ : ∀ {Γ i P rG lG t l}
     → ([Γ] : ⊩ᵛ Γ)
     → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
     → ([ΠP] : Γ ⊩ᵛ⟨ l ⟩ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ])
     → ([P] : Γ ⊩ᵛ⟨ l ⟩ P ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP])
     → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
     → Γ ⊩ᵛ⟨ l ⟩ (P ∘ t ^ ¹) ^ [ rG , ι lG ] / [Γ]
-- lG = ⁰: next ⁰ = ι ¹ matches substSΠ₁ / appTerm; univEq then lift ι ⁰ → l.
P∘tᵛ {i = i} {P = P} {rG = rG} {lG = ⁰} {t = t} {l = ∞} [Γ] [Ind] [ΠP] [P] [t]
      {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σInd] = proj₁ ([Ind] ⊢Δ [σ])
      [σΠP]  = proj₁ ([ΠP] ⊢Δ [σ])
      [σP]   = proj₁ ([P] ⊢Δ [σ])
      [σt]   = proj₁ ([t] ⊢Δ [σ])
      [σU]   = substSΠ₁ [σΠP] [σInd] [σt]
      [σU]′  = irrelevance′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t)) [σU]
      [σP∘t]ₜ = irrelevanceTerm′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t)) PE.refl PE.refl
                                 [σU] [σU]′
                                 (appTerm PE.refl [σInd] [σU] [σΠP] [σP] [σt])
      [σA]₀ = univEq [σU]′ [σP∘t]ₜ
      [σA]  = maybeEmb [σA]₀
  in  [σA]
    , (λ {σ′} [σ′] [σ≡σ′] →
         let [σ′Ind] = proj₁ ([Ind] ⊢Δ [σ′])
             [σ′t]   = proj₁ ([t] ⊢Δ [σ′])
             [σt′]   = convTerm₂ [σInd] [σ′Ind]
                                 (proj₂ ([Ind] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                 [σ′t]
             [σP≡]   = proj₂ ([P] ⊢Δ [σ]) [σ′] [σ≡σ′]
             [σt≡]   = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
             [σU≡]′  = irrelevanceEqTerm′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t))
                                          PE.refl PE.refl [σU] [σU]′
                                          (app-congTerm [σInd] [σU] [σΠP]
                                            [σP≡] [σt] [σt′] [σt≡])
         in  irrelevanceEq [σA]₀ [σA]
                           (univEqEq [σU]′ [σA]₀ [σU≡]′))
P∘tᵛ {i = i} {P = P} {rG = rG} {lG = ⁰} {t = t} {l = ι ¹} [Γ] [Ind] [ΠP] [P] [t]
      {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σInd] = proj₁ ([Ind] ⊢Δ [σ])
      [σΠP]  = proj₁ ([ΠP] ⊢Δ [σ])
      [σP]   = proj₁ ([P] ⊢Δ [σ])
      [σt]   = proj₁ ([t] ⊢Δ [σ])
      [σU]   = substSΠ₁ [σΠP] [σInd] [σt]
      [σU]′  = irrelevance′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t)) [σU]
      [σP∘t]ₜ = irrelevanceTerm′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t)) PE.refl PE.refl
                                 [σU] [σU]′
                                 (appTerm PE.refl [σInd] [σU] [σΠP] [σP] [σt])
      [σA]₀ = univEq [σU]′ [σP∘t]ₜ
      [σA]  = maybeEmb′ (<is≤ 0<1) [σA]₀
  in  [σA]
    , (λ {σ′} [σ′] [σ≡σ′] →
         let [σ′Ind] = proj₁ ([Ind] ⊢Δ [σ′])
             [σ′t]   = proj₁ ([t] ⊢Δ [σ′])
             [σt′]   = convTerm₂ [σInd] [σ′Ind]
                                 (proj₂ ([Ind] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                 [σ′t]
             [σP≡]   = proj₂ ([P] ⊢Δ [σ]) [σ′] [σ≡σ′]
             [σt≡]   = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
             [σU≡]′  = irrelevanceEqTerm′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t))
                                          PE.refl PE.refl [σU] [σU]′
                                          (app-congTerm [σInd] [σU] [σΠP]
                                            [σP≡] [σt] [σt′] [σt≡])
         in  irrelevanceEq [σA]₀ [σA]
                           (univEqEq [σU]′ [σA]₀ [σU≡]′))
P∘tᵛ {i = i} {P = P} {rG = rG} {lG = ⁰} {t = t} {l = ι ⁰} [Γ] [Ind] [ΠP] [P] [t]
      {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σInd] = proj₁ ([Ind] ⊢Δ [σ])
      [σΠP]  = proj₁ ([ΠP] ⊢Δ [σ])
      [σP]   = proj₁ ([P] ⊢Δ [σ])
      [σt]   = proj₁ ([t] ⊢Δ [σ])
      [σU]   = substSΠ₁ [σΠP] [σInd] [σt]
      [σU]′  = irrelevance′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t)) [σU]
      [σP∘t]ₜ = irrelevanceTerm′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t)) PE.refl PE.refl
                                 [σU] [σU]′
                                 (appTerm PE.refl [σInd] [σU] [σΠP] [σP] [σt])
      [σA] = univEq [σU]′ [σP∘t]ₜ
  in  [σA]
    , (λ {σ′} [σ′] [σ≡σ′] →
         let [σ′Ind] = proj₁ ([Ind] ⊢Δ [σ′])
             [σ′t]   = proj₁ ([t] ⊢Δ [σ′])
             [σt′]   = convTerm₂ [σInd] [σ′Ind]
                                 (proj₂ ([Ind] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                 [σ′t]
             [σP≡]   = proj₂ ([P] ⊢Δ [σ]) [σ′] [σ≡σ′]
             [σt≡]   = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
             [σU≡]′  = irrelevanceEqTerm′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ⁰) t))
                                          PE.refl PE.refl [σU] [σU]′
                                          (app-congTerm [σInd] [σU] [σΠP]
                                            [σP≡] [σt] [σt′] [σt≡])
         in  univEqEq [σU]′ [σA] [σU≡]′)
-- lG = ¹: Univ rG ¹ at TypeInfo ι ¹ (from Π annotation ° ¹) cannot be Uᵣ
-- (Uᵣ needs next l′ ≡ ι ¹ ⇒ l′ = ⁰, hence reduction to Univ _ ⁰, so ¹ ≡ ⁰).
-- Well-typed motives cannot use lG = ¹ (Univ r ¹ ∉ U ¹); discharge by contradiction.
P∘tᵛ {i = i} {P = P} {rG = rG} {lG = ¹} {t = t} {l = l} [Γ] [Ind] [ΠP] [P] [t]
      {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σInd] = proj₁ ([Ind] ⊢Δ [σ])
      [σΠP]  = proj₁ ([ΠP] ⊢Δ [σ])
      [σt]   = proj₁ ([t] ⊢Δ [σ])
      [σU]′  = irrelevance′ (PE.sym (singleSubstLift {σ = σ} (Univ rG ¹) t))
                           (substSΠ₁ [σΠP] [σInd] [σt])
  in  ⊥-elim (noUniv¹ι¹ [σU]′)
  where
    noUniv¹ι¹ : ∀ {Δ r l} → Δ ⊩⟨ l ⟩ Univ r ¹ ^ [ ! , ι ¹ ] → ⊥
    noUniv¹ι¹ (Uᵣ (Uᵣ _ ⁰ _ eq d)) =
      let _ , ¹≡⁰ = univRed* (red d)
      in  ⁰≢¹ (PE.sym ¹≡⁰)
    noUniv¹ι¹ (Uᵣ (Uᵣ _ ¹ _ () _))
    noUniv¹ι¹ [U]@(ne′ K D neK _) =
      U≢ne neK (whrDet* (id (escape [U]) , Uₙ) (red D , ne neK))
    noUniv¹ι¹ [U]@(Πᵣ′ _ _ _ _ _ _ _ D _ _ _ _ _ _) =
      U≢Π (whrDet* (id (escape [U]) , Uₙ) (red D , Πₙ))
    noUniv¹ι¹ {l = ι ¹} (emb emb< [U]) = noUniv¹ι¹ [U]
    noUniv¹ι¹ {l = ∞} (emb ∞< [U]) = noUniv¹ι¹ [U]


------------------------------------------------------------------------
-- Helpers shared by a future IndRectTerm / IndRectᵛ definition

private
  reflAllEq′ : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → Γ ⊢All ts ≡ ts ∷ As ^ r
  reflAllEq′ εⱼ = εⱼ
  reflAllEq′ (consⱼ {r = [ ! , l ]} ⊢t ⊢ts) = consⱼ (refl ⊢t) (reflAllEq′ ⊢ts)
  reflAllEq′ (consⱼ {r = [ % , l ]} ⊢t ⊢ts) = consⱼ (proof-irrelevance ⊢t ⊢t) (reflAllEq′ ⊢ts)

escapeMethodsσ : ∀ {Γ Δ σ i P rG lG ms l}
  → ([Γ] : ⊩ᵛ Γ)
  → (⊢Δ : ⊢ Δ)
  → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                    → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
         ms (indRectBranchTyList i P rG lG)
  → Δ ⊢All map (subst σ) ms ∷ indRectBranchTyList i (subst σ P) rG lG ^ [ rG , ι lG ]
escapeMethodsσ {Δ = Δ} {σ = σ} {i = i} {P = P} {rG = rG} {lG = lG} {ms = ms} [Γ] ⊢Δ [σ] [ms] =
  PE.subst (λ As → Δ ⊢All map (subst σ) ms ∷ As ^ [ rG , ι lG ])
           (subst-indRectBranchTyList σ i P rG lG)
           (go ms (indRectBranchTyList i P rG lG) [ms])
  where
    go : ∀ ms′ As →
      All₂ (λ m A → ∃ λ ([A] : _ ⊩ᵛ⟨ _ ⟩ A ^ [ rG , ι lG ] / _)
                      → _ ⊩ᵛ⟨ _ ⟩ m ∷ A ^ [ rG , ι lG ] / _ / [A]) ms′ As
      → Δ ⊢All map (subst σ) ms′ ∷ map (subst σ) As ^ [ rG , ι lG ]
    go []ₗ []ₗ []ₐ = εⱼ
    go (m ∷ₗ ms′) (A ∷ₗ As′) (([A] , [m]) ∷ₐ ps) =
      consⱼ (escapeTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([m] ⊢Δ [σ])))
            (go ms′ As′ ps)

------------------------------------------------------------------------
-- Validity of IndRect (natrec2ᵛ clone).
-- Extended with method All₂. Full IndRectTerm/congTerm definition still TODO.

postulate
  IndRectᵛ : ∀ {Γ i P rG lG t ms As l}
           → (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
           → ([Γ] : ⊩ᵛ Γ)
           → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
           → ([ΠP] : Γ ⊩ᵛ⟨ l ⟩ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ])
           → ([P] : Γ ⊩ᵛ⟨ l ⟩ P ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP])
           → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
           → ([P∘t] : Γ ⊩ᵛ⟨ l ⟩ (P ∘ t ^ ¹) ^ [ rG , ι lG ] / [Γ])
           → Γ ⊢All ms ∷ As ^ [ rG , ι lG ]
           → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                           → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                  ms As
           → Γ ⊩ᵛ⟨ l ⟩ IndRect i lG P t ms ∷ (P ∘ t ^ ¹) ^ [ rG , ι lG ] / [Γ] / [P∘t]


-- Type equality of motive applications (Univ bridge for IndRect-cong).
-- Avoids decompΠᵛ/app-congᵛ metas on the closed codomain Univ ! lG.
postulate
  P∘t-congᵛ : ∀ {Γ i P P' rG lG t t' l}
            → ([Γ] : ⊩ᵛ Γ)
            → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
            → ([ΠP] : Γ ⊩ᵛ⟨ l ⟩ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ])
            → ([ΠP'] : Γ ⊩ᵛ⟨ l ⟩ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ])
            → ([P] : Γ ⊩ᵛ⟨ l ⟩ P ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP])
            → ([P'] : Γ ⊩ᵛ⟨ l ⟩ P' ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP'])
            → ([P≡P'] : Γ ⊩ᵛ⟨ l ⟩ P ≡ P' ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP])
            → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
            → ([t'] : Γ ⊩ᵛ⟨ l ⟩ t' ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
            → ([t≡t'] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t' ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
            → ([P∘t] : Γ ⊩ᵛ⟨ l ⟩ (P ∘ t ^ ¹) ^ [ rG , ι lG ] / [Γ])
            → Γ ⊩ᵛ⟨ l ⟩ (P ∘ t ^ ¹) ≡ (P' ∘ t' ^ ¹) ^ [ rG , ι lG ] / [Γ] / [P∘t]

------------------------------------------------------------------------
-- Validity of the IndRect β-reduct (apps of the j-th method).
-- Corresponds to the RHS constructed by appᵛ in natrec-suc / natrec2-suc;
-- variable-arity apps make a direct clone impractical.
postulate
  IndRect-ctr-rhsᵛ : ∀ {Γ i j P rG lG args ms l}
                   → (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
                   → ([Γ] : ⊩ᵛ Γ)
                   → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
                   → ([d] : Γ ⊩ᵛ⟨ l ⟩ ctr i j args ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
                   → ([P∘d] : Γ ⊩ᵛ⟨ l ⟩ (P ∘ ctr i j args ^ ¹) ^ [ rG , ι lG ] / [Γ])
                   → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
                   → Γ ⊢All ms ∷ indRectBranchTyList i P rG lG ^ [ rG , ι lG ]
                   → Γ ⊩ᵛ⟨ l ⟩ apps lG (lookupDefault (ctr i j args) ms j)
                                        (args ++ map (λ a → IndRect i lG P a ms) args)
                              ∷ (P ∘ ctr i j args ^ ¹) ^ [ rG , ι lG ] / [Γ] / [P∘d]

------------------------------------------------------------------------
-- Validity of IndRect congruence.
-- ⊢ms' is under P (as in Typed IndRect-cong / ⊢All equality), not P'.
postulate
  IndRect-congᵛ : ∀ {i P P' rG lG t t' ms ms' Γ l}
              (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
              ([Γ] : ⊩ᵛ Γ)
              ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
              ([ΠP] : Γ ⊩ᵛ⟨ l ⟩ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ])
              ([ΠP'] : Γ ⊩ᵛ⟨ l ⟩ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ])
              ([P] : Γ ⊩ᵛ⟨ l ⟩ P ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP])
              ([P'] : Γ ⊩ᵛ⟨ l ⟩ P' ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP'])
              ([P≡P'] : Γ ⊩ᵛ⟨ l ⟩ P ≡ P' ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ] / [Γ] / [ΠP])
              ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              ([t'] : Γ ⊩ᵛ⟨ l ⟩ t' ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              ([t≡t'] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t' ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              ([P∘t] : Γ ⊩ᵛ⟨ l ⟩ (P ∘ t ^ ¹) ^ [ rG , ι lG ] / [Γ])
              (⊢ms : Γ ⊢All ms ∷ indRectBranchTyList i P ! lG ^ [ ! , ι lG ])
              (⊢ms' : Γ ⊢All ms' ∷ indRectBranchTyList i P ! lG ^ [ ! , ι lG ])
              (⊢ms≡ : Γ ⊢All ms ≡ ms' ∷ indRectBranchTyList i P ! lG ^ [ ! , ι lG ])
              (rG≡! : rG PE.≡ !)
            → Γ ⊩ᵛ⟨ l ⟩ IndRect i lG P t ms ≡ IndRect i lG P' t' ms' ∷ (P ∘ t ^ ¹) ^ [ rG , ι lG ] / [Γ] / [P∘t]

------------------------------------------------------------------------
