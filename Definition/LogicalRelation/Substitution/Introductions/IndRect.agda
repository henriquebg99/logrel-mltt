import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.IndRect (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}

open import Definition.Untyped senv
open import Definition.Untyped.Properties senv
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.RedSteps senv equivs
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.ShapeView senv equivs
open import Definition.LogicalRelation.Irrelevance senv equivs
open import Definition.LogicalRelation.Properties senv equivs
open import Definition.LogicalRelation.Application senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Application senv equivs
open import Definition.LogicalRelation.Substitution senv equivs
open import Definition.LogicalRelation.Substitution.Properties senv equivs
open import Definition.LogicalRelation.Substitution.Escape senv equivs
open import Definition.LogicalRelation.Substitution.Reflexivity senv equivs
import Definition.LogicalRelation.Substitution.Irrelevance senv equivs as S
open import Definition.LogicalRelation.Substitution.Introductions.Ind senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Cast senv equivs using (inversion-Ctr)
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst senv equivs
open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Nullary using (Dec; yes; no)
open import Tools.List using (List; All; All₂; All₃; range-suc; ∷-inj₁; ∷-inj₂; []ₐ; _∷ₐ_; map; _++_; lookupDefault; nth; length; length-map; All₂-length; lookupAll₂; all∈; length-range;
                              replicate; length-replicate; range; zip; foldr; _∈ₗ_; hereₗ; thereₗ;
                              nth-length; nth-map; nth-zip-range; nth-lookupDefault; nthAll₂; nthAll₃)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Tools.Maybe using (just)
open import Tools.Inequality using (Bool; true; false; eqb; eqb-refl; if_then_else_; filter)
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU
import Definition.OUntyped senv as O

IndRect-subst* : ∀ {Γ ind P lG t t′ ms l}
               → ind ∈ₗ senv
               → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ^ [ ! , ι lG ]
               → Γ ⊢ t ⇒* t′ ∷ Ind (SU.SInd.name ind) ^ ι ⁰
               → Γ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
               → ([Ind] : Γ ⊩⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ])
               → Γ ⊩⟨ l ⟩ t′ ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Ind]
               → (∀ {u u′} → Γ ⊩⟨ l ⟩ u ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Ind]
                           → Γ ⊩⟨ l ⟩ u′ ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Ind]
                           → Γ ⊩⟨ l ⟩ u ≡ u′ ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Ind]
                           → Γ ⊢ P [ u ] ≡ P [ u′ ] ^ [ ! , ι lG ])
               → Γ ⊢ IndRect (SU.SInd.name ind) lG P t ms ⇒* IndRect (SU.SInd.name ind) lG P t′ ms
                     ∷ P [ t ] ^ ι lG
IndRect-subst* ind∈ ⊢P (id ⊢t) ⊢ms [Ind] [t′] prop = id (IndRectⱼ (λ ()) ind∈ ⊢P ⊢t ⊢ms)
IndRect-subst* ind∈ ⊢P (x ⇨ t⇒t′) ⊢ms [Ind] [t′] prop =
  let q , w = redSubst*Term t⇒t′ [Ind] [t′]
      a , s = redSubstTerm x [Ind] q
  in  IndRect-subst ind∈ ⊢P x ⊢ms
      ⇨ conv* (IndRect-subst* ind∈ ⊢P t⇒t′ ⊢ms [Ind] [t′] prop)
              (prop q a (symEqTerm [Ind] s))

------------------------------------------------------------------------
-- Helpers shared by a future IndRectTerm / IndRectᵛ definition

private
  reflAllEq′ : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → Γ ⊢All ts ≡ ts ∷ As ^ r
  reflAllEq′ εⱼ = εⱼ
  reflAllEq′ (consⱼ {r = [ ! , l ]} ⊢t ⊢ts) = consⱼ (refl ⊢t) (reflAllEq′ ⊢ts)
  reflAllEq′ (consⱼ {r = [ % , l ]} ⊢t ⊢ts) = consⱼ (proof-irrelevance ⊢t ⊢t) (reflAllEq′ ⊢ts)

escapeMethodsσ : ∀ {Γ Δ σ ind P rG lG ms l}
  → ([Γ] : ⊩ᵛ Γ)
  → (⊢Δ : ⊢ Δ)
  → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                    → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
         ms (indRectBranchTyList ind P rG lG)
  → Δ ⊢All map (subst σ) ms ∷ indRectBranchTyList ind (subst (liftSubst σ) P) rG lG ^ [ rG , ι lG ]
escapeMethodsσ {Δ = Δ} {σ = σ} {ind = ind} {P = P} {rG = rG} {lG = lG} {ms = ms} [Γ] ⊢Δ [σ] [ms] =
  PE.subst (λ As → Δ ⊢All map (subst σ) ms ∷ As ^ [ rG , ι lG ])
           (subst-indRectBranchTyList σ ind P rG lG)
           (go ms (indRectBranchTyList ind P rG lG) [ms])
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
-- Shape of the constructor-argument list.
-- Positivity forces every constructor argument of Ind i to be Ind i itself,
-- so every argument is recursive and the recursive-index list is range n.

ctrArity : List SU.Type → Nat
ctrArity Ts = length Ts

private
  allPos-replicate : ∀ {i} Ts → All (SU.isPositive i) Ts
                   → Ts PE.≡ replicate (length Ts) (SU.Ind i)
  allPos-replicate []ₗ []ₐ = PE.refl
  allPos-replicate (SU.Ind j ∷ₗ Ts) (pos ∷ₐ ps) =
    PE.cong₂ _∷ₗ_ (PE.cong SU.Ind (PE.sym pos)) (allPos-replicate Ts ps)
  allPos-replicate (SU.Arrow _ _ ∷ₗ _) (() ∷ₐ _)

  filter-zip-rep : ∀ i (ns : List Nat) m →
    filter (λ jT → SU.ctrArgIsRecursive i (proj₂ jT)) (zip ns (replicate m (SU.Ind i)))
    PE.≡ zip ns (replicate m (SU.Ind i))
  filter-zip-rep i []ₗ m = PE.refl
  filter-zip-rep i (x ∷ₗ ns) 0 = PE.refl
  filter-zip-rep i (x ∷ₗ ns) (1+ m) rewrite eqb-refl i =
    PE.cong ((x , SU.Ind i) ∷ₗ_) (filter-zip-rep i ns m)

  map-proj₁-zip : ∀ {A : Set} (ns : List Nat) (xs : List A)
                → length ns PE.≡ length xs → map proj₁ (zip ns xs) PE.≡ ns
  map-proj₁-zip []ₗ xs eq = PE.refl
  map-proj₁-zip (n ∷ₗ ns) []ₗ ()
  map-proj₁-zip (n ∷ₗ ns) (x ∷ₗ xs) eq =
    PE.cong (n ∷ₗ_) (map-proj₁-zip ns xs (PE.cong pred eq))

ctrArgs-replicate : ∀ i Ts → All (SU.isPositive i) Ts →
  Ts PE.≡ replicate (ctrArity Ts) (SU.Ind i)
ctrArgs-replicate i Ts pos = allPos-replicate Ts pos

ctrRecIndices-range : ∀ i Ts → All (SU.isPositive i) Ts →
  ctrRecIndices i Ts PE.≡ range (ctrArity Ts)
ctrRecIndices-range i Ts pos = go i (ctrArity Ts) Ts (ctrArgs-replicate i Ts pos)
  where
    go : ∀ i n (as : List SU.Type) → as PE.≡ replicate n (SU.Ind i)
       → map proj₁ (filter (λ jT → SU.ctrArgIsRecursive i (proj₂ jT))
                           (zip (range (length as)) as))
         PE.≡ range (length as)
    go i n .(replicate n (SU.Ind i)) PE.refl
      rewrite length-replicate n (SU.Ind i) =
      PE.trans (PE.cong (map proj₁) (filter-zip-rep i (range n) n))
               (map-proj₁-zip (range n) (replicate n (SU.Ind i))
                  (PE.trans (length-range n) (PE.sym (length-replicate n (SU.Ind i)))))

ctrArgTys-replicate : ∀ i Ts → All (SU.isPositive i) Ts →
  map proj₁ (ctrArgsTypeList Ts) PE.≡ replicate (ctrArity Ts) (Ind i)
ctrArgTys-replicate i Ts pos =
  PE.trans (embArgTys Ts)
    (PE.trans (PE.cong (map emb-stype) (ctrArgs-replicate i Ts pos))
              (map-emb-replicate (ctrArity Ts)))
  where
    embArgTys : ∀ Ts →
      map proj₁ (ctrArgsTypeList Ts) PE.≡ map emb-stype Ts
    embArgTys Ts =
      PE.trans (map-map proj₁ (λ p → (emb_oterm_term (proj₁ p) , proj₂ p))
                        (O.ctrArgsTypeList Ts))
        (PE.trans (map-map (λ p → emb_oterm_term (proj₁ p))
                           (λ T → (O.emb-stype-oterm T , 0))
                           Ts)
                  (map-cong Ts emb-stype-hom))

    map-emb-replicate : ∀ n →
      map emb-stype (replicate n (SU.Ind i)) PE.≡ replicate n (Ind i)
    map-emb-replicate 0 = PE.refl
    map-emb-replicate (1+ n) = PE.cong (Ind i ∷ₗ_) (map-emb-replicate n)

------------------------------------------------------------------------
-- Telescopes.
-- Both phases of a method type are Π-telescopes built with foldr; the
-- hypothesis phase is in fact a chain of non-dependent arrows.

private
  -- Π former of a telescope step (domain level lD, codomain level lG).
  Πt : Level → Level → Term → Term → Term
  Πt lD lG A B = Π A ^ ! ° lD ▹ B ° lG ° lG ^ !

  -- Iterated non-dependent arrow.
  arrows : Level → List Term → Term → Term
  arrows lG []ₗ E = E
  arrows lG (D ∷ₗ Ds) E = Πt lG lG D (wk1 (arrows lG Ds E))

  -- Telescope of hypotheses that do not depend on each other:
  -- the p-th entry is weakened p times.
  wkTele : List Term → List Term
  wkTele []ₗ = []ₗ
  wkTele (D ∷ₗ Ds) = D ∷ₗ map wk1 (wkTele Ds)

  length-wkTele : ∀ Ds → length (wkTele Ds) PE.≡ length Ds
  length-wkTele []ₗ = PE.refl
  length-wkTele (D ∷ₗ Ds) =
    PE.cong 1+ (PE.trans (length-map wk1 (wkTele Ds)) (length-wkTele Ds))

  -- Weakening of a telescope: the p-th entry is weakened under p lifts.
  wkTel : Wk → List Term → List Term
  wkTel ρ []ₗ = []ₗ
  wkTel ρ (A ∷ₗ As) = wk ρ A ∷ₗ wkTel (lift ρ) As

  repeat-lift-lift : ∀ ρ n → repeat lift (lift ρ) n PE.≡ lift (repeat lift ρ n)
  repeat-lift-lift ρ 0 = PE.refl
  repeat-lift-lift ρ (1+ n) = PE.cong lift (repeat-lift-lift ρ n)

  wk-foldr : ∀ ρ lD lG (L : List Term) Z →
    wk ρ (foldr (Πt lD lG) Z L) PE.≡
    foldr (Πt lD lG) (wk (repeat lift ρ (length L)) Z) (wkTel ρ L)
  wk-foldr ρ lD lG []ₗ Z = PE.refl
  wk-foldr ρ lD lG (A ∷ₗ L) Z =
    PE.cong (Πt lD lG (wk ρ A))
      (PE.trans (wk-foldr (lift ρ) lD lG L Z)
        (PE.cong (λ ρ′ → foldr (Πt lD lG) (wk ρ′ Z) (wkTel (lift ρ) L))
                 (repeat-lift-lift ρ (length L))))

  wk1-wk1^ : ∀ p X → wk1^ p (wk1 X) PE.≡ wk1 (wk1^ p X)
  wk1-wk1^ 0 X = PE.refl
  wk1-wk1^ (1+ p) X = PE.cong wk1 (wk1-wk1^ p X)

  wk1^-wk : ∀ p X → wk (repeat lift (step id) p) (wk1^ p X) PE.≡ wk1^ p (wk1 X)
  wk1^-wk 0 X = PE.refl
  wk1^-wk (1+ p) X =
    PE.trans (PE.sym (wk1-wk≡lift-wk1 (repeat lift (step id) p) (wk1^ p X)))
             (PE.cong wk1 (wk1^-wk p X))

  -- Iterated map wk1 over a telescope.
  mapwk1^ : Nat → List Term → List Term
  mapwk1^ 0 L = L
  mapwk1^ (1+ p) L = mapwk1^ p (map wk1 L)

  mapwk1^-[] : ∀ p → mapwk1^ p []ₗ PE.≡ []ₗ
  mapwk1^-[] 0 = PE.refl
  mapwk1^-[] (1+ p) = mapwk1^-[] p

  mapwk1^-∷ : ∀ p D L → mapwk1^ p (D ∷ₗ L) PE.≡ wk1^ p D ∷ₗ mapwk1^ p L
  mapwk1^-∷ 0 D L = PE.refl
  mapwk1^-∷ (1+ p) D L =
    PE.trans (mapwk1^-∷ p (wk1 D) (map wk1 L))
             (PE.cong (_∷ₗ mapwk1^ p (map wk1 L)) (wk1-wk1^ p D))

  wkTel-wkTele : ∀ Ds → wkTel (step id) (wkTele Ds) PE.≡ map wk1 (wkTele Ds)
  wkTel-wkTele Ds = go 0 Ds
    where
      go : ∀ p Ds → wkTel (repeat lift (step id) p) (mapwk1^ p (wkTele Ds))
                    PE.≡ map wk1 (mapwk1^ p (wkTele Ds))
      go p []ₗ rewrite mapwk1^-[] p = PE.refl
      go p (D ∷ₗ Ds) rewrite mapwk1^-∷ p D (map wk1 (wkTele Ds)) =
        PE.cong₂ _∷ₗ_ (PE.trans (wk1^-wk p D) (wk1-wk1^ p D)) (go (1+ p) Ds)

  arrows-foldr : ∀ lG (Ds : List Term) E →
    foldr (Πt lG lG) (wk1^ (length Ds) E) (wkTele Ds) PE.≡ arrows lG Ds E
  arrows-foldr lG []ₗ E = PE.refl
  arrows-foldr lG (D ∷ₗ Ds) E =
    PE.cong (Πt lG lG D)
      (PE.trans
        (PE.cong₂ (λ Z L → foldr (Πt lG lG) Z L)
          (PE.trans (PE.sym (wk1-wk1^ (length Ds) E))
                    (PE.sym (wk1^-wk (length Ds) E)))
          (PE.sym (wkTel-wkTele Ds)))
        (PE.trans
          (PE.cong (λ m → foldr (Πt lG lG)
                            (wk (repeat lift (step id) m) (wk1^ (length Ds) E))
                            (wkTel (step id) (wkTele Ds)))
                   (PE.sym (length-wkTele Ds)))
          (PE.trans (PE.sym (wk-foldr (step id) lG lG (wkTele Ds) (wk1^ (length Ds) E)))
                    (PE.cong wk1 (arrows-foldr lG Ds E)))))

------------------------------------------------------------------------
-- Instantiation of the argument binders of a method type.

private
  wk1^-plus : ∀ m n X → wk1^ (m + n) X PE.≡ wk1^ m (wk1^ n X)
  wk1^-plus 0 n X = PE.refl
  wk1^-plus (1+ m) n X = PE.cong wk1 (wk1^-plus m n X)

  repeat-liftSubst-lift : ∀ σ n →
    repeat liftSubst (liftSubst σ) n PE.≡ liftSubst (repeat liftSubst σ n)
  repeat-liftSubst-lift σ 0 = PE.refl
  repeat-liftSubst-lift σ (1+ n) = PE.cong liftSubst (repeat-liftSubst-lift σ n)

  subst-wk1^ : ∀ n σ t →
    subst (repeat liftSubst σ n) (wk1^ n t) PE.≡ wk1^ n (subst σ t)
  subst-wk1^ 0 σ t = PE.refl
  subst-wk1^ (1+ n) σ t =
    PE.trans (Idsym-subst-lemma (repeat liftSubst σ n) (wk1^ n t))
             (PE.cong wk1 (subst-wk1^ n σ t))

  substVar-lifts-< : ∀ n σ x → x << n → repeat liftSubst σ n x PE.≡ var x
  substVar-lifts-< (1+ n) σ 0 (leS _) = PE.refl
  substVar-lifts-< (1+ n) σ (1+ x) (leS p) =
    PE.cong wk1 (substVar-lifts-< n σ x p)

  substVar-lifts-≥ : ∀ n σ y → repeat liftSubst σ n (n + y) PE.≡ wk1^ n (σ y)
  substVar-lifts-≥ 0 σ y = PE.refl
  substVar-lifts-≥ (1+ n) σ y = PE.cong wk1 (substVar-lifts-≥ n σ y)

  minus-<- : ∀ n r → r << n → ((n - 1) - r) << n
  minus-<- (1+ n) 0 (leS _) = leS (le-refl n)
  minus-<- (1+ n) (1+ r) (leS p) =
    le-suc (PE.subst (_<< n) (PE.sym (minus-suc n r)) (minus-<- n r p))

  -- The substitution instantiating the n argument binders with as.
  argSubst : List Term → Subst
  argSubst []ₗ = idSubst
  argSubst (a ∷ₗ as) = argSubst as ₛ•ₛ repeat liftSubst (sgSubst a) (length as)

  argSubst-wk : ∀ as X → subst (argSubst as) (wk1^ (length as) X) PE.≡ X
  argSubst-wk []ₗ X = subst-id X
  argSubst-wk (a ∷ₗ as) X =
    PE.trans (PE.sym (substCompEq (wk1^ (1+ (length as)) X)))
      (PE.trans
        (PE.cong (subst (argSubst as))
          (PE.trans (PE.cong (subst (repeat liftSubst (sgSubst a) (length as)))
                             (PE.sym (wk1-wk1^ (length as) X)))
            (PE.trans (subst-wk1^ (length as) (sgSubst a) (wk1 X))
                      (PE.cong (wk1^ (length as)) (wk1-singleSubst X a)))))
        (argSubst-wk as X))

  argSubst-var : ∀ as p → p << length as →
    subst (argSubst as) (var ((length as - 1) - p)) PE.≡ lookupDefault (var 0) as p
  argSubst-var []ₗ p ()
  argSubst-var (a ∷ₗ as) 0 (leS _) =
    PE.trans (PE.cong (λ x → subst (argSubst as)
                               (repeat liftSubst (sgSubst a) (length as) x))
                      (PE.sym (plusZero (length as))))
      (PE.trans (PE.cong (subst (argSubst as))
                         (substVar-lifts-≥ (length as) (sgSubst a) 0))
                (argSubst-wk as a))
  argSubst-var (a ∷ₗ as) (1+ p) (leS h) =
    PE.trans (PE.cong (λ x → subst (argSubst as)
                               (repeat liftSubst (sgSubst a) (length as) x))
                      (minus-suc (length as) p))
      (PE.trans (PE.cong (subst (argSubst as))
                         (substVar-lifts-< (length as) (sgSubst a)
                            ((length as - 1) - p) (minus-<- (length as) p h)))
                (argSubst-var as p h))

------------------------------------------------------------------------
-- Normal form of a method type once its argument binders are instantiated.
-- Substituting the n arguments collapses the hypothesis phase into the
-- chain of non-dependent arrows (P ∘ a₀) ▹▹ … ▹▹ (P ∘ ctr i j as).

private
  Πarg : Relevance → Level → Term → Term → Term
  Πarg rG lG A B = Π A ^ ! ° ⁰ ▹ B ° lG ° lG ^ rG

  Πih : Relevance → Level → Term → Term → Term
  Πih rG lG A B = Π A ^ rG ° lG ▹ B ° lG ° lG ^ rG

  -- The hypothesis telescope and the conclusion of a method type, with
  -- the recursive-index list already known to be range n.
  ihFun : Nat → Term → Nat → Nat → Term
  ihFun n Q r ℓ = Q [ var (((n - 1) - r) + ℓ) ]↑^ (n + ℓ)

  ihGo : Nat → Term → Nat → List Nat → List Term
  ihGo n Q ℓ []ₗ = []ₗ
  ihGo n Q ℓ (r ∷ₗ rs) = ihFun n Q r ℓ ∷ₗ ihGo n Q (1+ ℓ) rs

  length-ihGo : ∀ n Q ℓ rs → length (ihGo n Q ℓ rs) PE.≡ length rs
  length-ihGo n Q ℓ []ₗ = PE.refl
  length-ihGo n Q ℓ (r ∷ₗ rs) = PE.cong 1+ (length-ihGo n Q (1+ ℓ) rs)

  ihGo-≡ : ∀ n Q ℓ rs →
    ihGo n Q ℓ rs PE.≡
    map (λ pj → ihFun n Q (proj₁ pj) (proj₂ pj))
        (zip rs (map (_+_ ℓ) (range (length rs))))
  ihGo-≡ n Q ℓ []ₗ = PE.refl
  ihGo-≡ n Q ℓ (r ∷ₗ rs) =
    let m = length rs
        f = λ pj → ihFun n Q (proj₁ pj) (proj₂ pj)
    in PE.trans
         (PE.cong (ihFun n Q r ℓ ∷ₗ_) (ihGo-≡ n Q (1+ ℓ) rs))
         (PE.sym
           (PE.trans
             (PE.cong (λ ns → map f (zip (r ∷ₗ rs) (map (_+_ ℓ) ns))) (range-suc m))
             (PE.trans
               (PE.cong (λ ℓ′ → f (r , ℓ′) ∷ₗ
                                map f (zip rs (map (_+_ ℓ) (map 1+ (range m)))))
                        (plusZero ℓ))
               (PE.cong (λ ys → f (r , ℓ) ∷ₗ map f (zip rs ys))
                 (PE.trans (map-map (_+_ ℓ) 1+ (range m))
                   (map-cong (range m) (λ x → plusSuc ℓ x)))))))

  ihGo-range : ∀ n Q rs →
    ihGo n Q 0 rs PE.≡
    map (λ pj → ihFun n Q (proj₁ pj) (proj₂ pj)) (zip rs (range (length rs)))
  ihGo-range n Q rs =
    PE.trans (ihGo-≡ n Q 0 rs)
      (PE.cong (λ ns → map (λ pj → ihFun n Q (proj₁ pj) (proj₂ pj)) (zip rs ns))
        (map-+0 (range (length rs))))
    where
    map-+0 : ∀ xs → map (_+_ 0) xs PE.≡ xs
    map-+0 []ₗ = PE.refl
    map-+0 (x ∷ₗ xs) = PE.cong (x ∷ₗ_) (map-+0 xs)

  ctrVars : Nat → List Term
  ctrVars n = map (λ v → var (((n + n) - 1) - v)) (range n)

  concl : Nat → Nat → Term → Nat → Term
  concl i j P n = P [ ctr i j (ctrVars n) ]↑^ (n + n)

  arity≡ : ∀ Ts → length (ctrArgsTypeList Ts) PE.≡ ctrArity Ts
  arity≡ Ts =
    PE.trans (length-map (λ p → (emb_oterm_term (proj₁ p) , proj₂ p))
                         (O.ctrArgsTypeList Ts))
             (length-map (λ T → (O.emb-stype-oterm T , 0)) Ts)

-- Method types are argument telescopes over constructor-arity many copies
-- of Ind i, followed by exactly as many induction hypotheses.
branchTy-nf : ∀ i j Ts P rG lG → All (SU.isPositive i) Ts →
  indRectBranchTy i j Ts P rG lG PE.≡
  foldr (Πarg rG lG)
    (foldr (Πih rG lG) (concl i j P (ctrArity Ts))
                       (ihGo (ctrArity Ts) P 0 (range (ctrArity Ts))))
    (replicate (ctrArity Ts) (Ind i))
branchTy-nf i j Ts P rG lG pos
  rewrite ctrArgTys-replicate i Ts pos | ctrRecIndices-range i Ts pos
        | arity≡ Ts | length-range (ctrArity Ts) =
  PE.cong (λ L → foldr (Πarg rG lG)
                   (foldr (Πih rG lG) (concl i j P (ctrArity Ts)) L)
                   (replicate (ctrArity Ts) (Ind i)))
    (PE.sym (PE.trans (ihGo-range (ctrArity Ts) P (range (ctrArity Ts)))
              (PE.cong (λ m → map (λ pj → ihFun (ctrArity Ts) P (proj₁ pj) (proj₂ pj))
                                  (zip (range (ctrArity Ts)) (range m)))
                       (length-range (ctrArity Ts)))))

private
  -- Substitution through a Π-telescope (clone of the local helpers of
  -- subst-indRectBranchTy, which are not exported).
  subst-tel : Subst → Nat → List Term → List Term
  subst-tel σ i []ₗ = []ₗ
  subst-tel σ i (A ∷ₗ As) = subst (repeat liftSubst σ i) A ∷ₗ subst-tel σ (1+ i) As

  tel-liftSubst : ∀ σ i As → subst-tel (liftSubst σ) i As PE.≡ subst-tel σ (1+ i) As
  tel-liftSubst σ i []ₗ = PE.refl
  tel-liftSubst σ i (A ∷ₗ As) =
    PE.cong₂ _∷ₗ_
      (PE.cong (λ σ′ → subst σ′ A) (repeat-liftSubst-lift σ i))
      (tel-liftSubst σ (1+ i) As)

  subst-foldr-Π : ∀ σ rA lA l r Z As →
    subst σ (foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r) Z As) PE.≡
    foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r)
          (subst (repeat liftSubst σ (length As)) Z)
          (subst-tel σ 0 As)
  subst-foldr-Π σ rA lA l r Z []ₗ = PE.refl
  subst-foldr-Π σ rA lA l r Z (A ∷ₗ As) =
    PE.cong₂ (λ A′ B′ → Π A′ ^ rA ° lA ▹ B′ ° l ° l ^ r)
      PE.refl
      (PE.trans (subst-foldr-Π (liftSubst σ) rA lA l r Z As)
        (PE.trans
          (PE.cong (λ σ′ → foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r)
                             (subst σ′ Z) (subst-tel (liftSubst σ) 0 As))
                   (repeat-liftSubst-lift σ (length As)))
          (PE.cong (foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r)
                     (subst (liftSubst (repeat liftSubst σ (length As))) Z))
                   (tel-liftSubst σ 0 As))))

  subst-foldr-Π-closed : ∀ σ rA lA l r Z As →
    (∀ σ' → map (subst σ') As PE.≡ As) →
    subst σ (foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r) Z As) PE.≡
    foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r)
          (subst (repeat liftSubst σ (length As)) Z) As
  subst-foldr-Π-closed σ rA lA l r Z []ₗ clo = PE.refl
  subst-foldr-Π-closed σ rA lA l r Z (A ∷ₗ As) clo =
    PE.cong₂ (λ A′ B′ → Π A′ ^ rA ° lA ▹ B′ ° l ° l ^ r)
      (∷-inj₁ (clo σ))
      (PE.trans (subst-foldr-Π-closed (liftSubst σ) rA lA l r Z As
                   (λ σ' → ∷-inj₂ (clo σ')))
        (PE.cong (λ σ′ → foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r)
                           (subst σ′ Z) As)
                 (repeat-liftSubst-lift σ (length As))))

  -- Argument telescopes of method types are closed.
  subst-replicate-Ind : ∀ σ n i →
    map (subst σ) (replicate n (Ind i)) PE.≡ replicate n (Ind i)
  subst-replicate-Ind σ 0 i = PE.refl
  subst-replicate-Ind σ (1+ n) i = PE.cong (Ind i ∷ₗ_) (subst-replicate-Ind σ n i)

private
  -- Small arithmetic and list lemmas used to compute the instantiation.
  wk1^-∘ : ∀ d A B l → wk1^ d (A ∘ B ^ l) PE.≡ wk1^ d A ∘ wk1^ d B ^ l
  wk1^-∘ 0 A B l = PE.refl
  wk1^-∘ (1+ d) A B l = PE.cong wk1 (wk1^-∘ d A B l)

  map-wk1^0 : ∀ (ts : List Term) → map (wk1^ 0) ts PE.≡ ts
  map-wk1^0 []ₗ = PE.refl
  map-wk1^0 (t ∷ₗ ts) = PE.cong (t ∷ₗ_) (map-wk1^0 ts)

  wk1^-ctr : ∀ n i j ts → wk1^ n (ctr i j ts) PE.≡ ctr i j (map (wk1^ n) ts)
  wk1^-ctr 0 i j ts = PE.cong (ctr i j) (PE.sym (map-wk1^0 ts))
  wk1^-ctr (1+ n) i j ts =
    PE.trans (PE.cong wk1 (wk1^-ctr n i j ts))
      (PE.trans (wk-ctr (step id) i j (map (wk1^ n) ts))
        (PE.cong (ctr i j) (map-map wk1 (wk1^ n) ts)))

  plus-minus : ∀ a b v → v <= b → ((a + b) - v) PE.≡ a + (b - v)
  plus-minus a b 0 _ = PE.refl
  plus-minus a 0 (1+ v) ()
  plus-minus a (1+ b) (1+ v) (leS h) =
    PE.trans (PE.cong (λ m → m - (1+ v)) (plusSuc a b)) (plus-minus a b v h)

  varIdx : ∀ n v → v << n → (((n + n) - 1) - v) PE.≡ n + ((n - 1) - v)
  varIdx n v h =
    PE.trans (PE.sym (minus-suc (n + n) v))
      (PE.trans (plus-minus n n (1+ v) h) (PE.cong (_+_ n) (minus-suc n v)))

  lookupDefault-map : ∀ {A B : Set} (f : A → B) (d : A) (e : B) xs q →
    q << length xs → lookupDefault e (map f xs) q PE.≡ f (lookupDefault d xs q)
  lookupDefault-map f d e []ₗ q ()
  lookupDefault-map f d e (x ∷ₗ xs) 0 _ = PE.refl
  lookupDefault-map f d e (x ∷ₗ xs) (1+ q) (leS h) = lookupDefault-map f d e xs q h

  lookup-range : ∀ n q → q << n → lookupDefault 0 (range n) q PE.≡ q
  lookup-range 0 q ()
  lookup-range (1+ n) q h =
    PE.trans (PE.cong (λ xs → lookupDefault 0 xs q) (range-suc n)) (aux q h)
    where
    aux : ∀ q → q << 1+ n → lookupDefault 0 (0 ∷ₗ map 1+ (range n)) q PE.≡ q
    aux 0 _ = PE.refl
    aux (1+ q) (leS h) =
      PE.trans (lookupDefault-map 1+ 0 0 (range n) q
                 (PE.subst (λ m → q << m) (PE.sym (length-range n)) h))
               (PE.cong 1+ (lookup-range n q h))

  map-range-≡ : ∀ {A : Set} (d : A) (f : Nat → A) (xs : List A) →
    (∀ q → q << length xs → f q PE.≡ lookupDefault d xs q) →
    map f (range (length xs)) PE.≡ xs
  map-range-≡ d f []ₗ h = PE.refl
  map-range-≡ d f (x ∷ₗ xs) h =
    PE.trans (PE.cong (map f) (range-suc (length xs)))
      (PE.cong₂ _∷ₗ_ (h 0 (leS le0))
        (PE.trans (map-map f 1+ (range (length xs)))
          (map-range-≡ d (λ q → f (1+ q)) xs (λ q hq → h (1+ q) (leS hq)))))

private
  -- Substitution lemmas for the pattern P [ u ]↑^ d.
  wk1^-var : ∀ d y → wk1^ d (var y) PE.≡ var (d + y)
  wk1^-var 0 y = PE.refl
  wk1^-var (1+ d) y = PE.cong wk1 (wk1^-var d y)

  wk1^Subst-app : ∀ d τ x → wk1^Subst d τ x PE.≡ wk1^ d (τ x)
  wk1^Subst-app 0 τ x = PE.refl
  wk1^Subst-app (1+ d) τ x = PE.cong wk1 (wk1^Subst-app d τ x)

  wk1^Subst-var : ∀ d x → wk1^Subst d idSubst x PE.≡ var (d + x)
  wk1^Subst-var 0 x = PE.refl
  wk1^Subst-var (1+ d) x = PE.cong wk1 (wk1^Subst-var d x)

  wk1^-subst : ∀ d τ X → wk1^ d (subst τ X) PE.≡ subst (wk1^Subst d τ) X
  wk1^-subst 0 τ X = PE.refl
  wk1^-subst (1+ d) τ X =
    PE.trans (PE.cong wk1 (wk1^-subst d τ X)) (wk-subst X)

  argSubst-shift : ∀ as y → argSubst as (length as + y) PE.≡ var y
  argSubst-shift as y =
    PE.trans (PE.sym (PE.cong (subst (argSubst as)) (wk1^-var (length as) y)))
             (argSubst-wk as (var y))

  -- Instantiating a motive pattern: a substitution which sends the n
  -- variables above d to the identity and u to b instantiates
  -- P [ u ]↑^ (n + d) to wk1^ d (P [ b ]).
  subst-Pat : ∀ σ n P d u b →
    (∀ x → σ (n + x) PE.≡ var x) →
    subst (repeat liftSubst σ d) u PE.≡ wk1^ d b →
    subst (repeat liftSubst σ d) (P [ u ]↑^ (n + d)) PE.≡ wk1^ d (P [ b ])
  subst-Pat σ n P d u b hσ hu =
    PE.trans (substCompEq P)
      (PE.trans (substVar-to-subst aux P)
                (PE.sym (wk1^-subst d (sgSubst b) P)))
    where
    aux : ∀ x → (repeat liftSubst σ d ₛ•ₛ consSubst (wk1^Subst (n + d) idSubst) u) x
              PE.≡ wk1^Subst d (sgSubst b) x
    aux 0 = PE.trans hu (PE.sym (wk1^Subst-app d (sgSubst b) 0))
    aux (1+ y) =
      PE.trans
        (PE.cong (subst (repeat liftSubst σ d)) (wk1^Subst-var (n + d) y))
        (PE.trans
          (PE.cong (repeat liftSubst σ d)
            (PE.trans (PE.cong (λ m → m + y) (plus-comm n d))
                      (PE.sym (plus-assoc d n y))))
          (PE.trans (substVar-lifts-≥ d σ (n + y))
            (PE.trans (PE.cong (wk1^ d) (hσ y))
                      (PE.sym (wk1^Subst-app d (sgSubst b) (1+ y))))))

private
  -- Instantiating the hypothesis telescope: the ℓ-th hypothesis becomes
  -- wk1^ ℓ (P [ aℓ ]).
  subst-tel-inst : ∀ σ n P d (rs : List Nat) (bs : List Term) →
    length rs PE.≡ length bs →
    (∀ x → σ (n + x) PE.≡ var x) →
    (∀ q → q << length rs →
       subst σ (var ((n - 1) - lookupDefault 0 rs q)) PE.≡ lookupDefault (var 0) bs q) →
    subst-tel σ d (ihGo n P d rs) PE.≡
    mapwk1^ d (wkTele (map (λ b → P [ b ]) bs))
  subst-tel-inst σ n P d []ₗ []ₗ len hσ hv = PE.sym (mapwk1^-[] d)
  subst-tel-inst σ n P d []ₗ (b ∷ₗ bs) () hσ hv
  subst-tel-inst σ n P d (r ∷ₗ rs) []ₗ () hσ hv
  subst-tel-inst σ n P d (r ∷ₗ rs) (b ∷ₗ bs) len hσ hv =
    PE.trans
      (PE.cong₂ _∷ₗ_ headEq
        (subst-tel-inst σ n P (1+ d) rs bs (PE.cong pred len) hσ
          (λ q hq → hv (1+ q) (leS hq))))
      (PE.sym (mapwk1^-∷ d (P [ b ]) (map wk1 (wkTele (map (λ b → P [ b ]) bs)))))
    where
    headEq : subst (repeat liftSubst σ d) (ihFun n P r d) PE.≡ wk1^ d (P [ b ])
    headEq =
      subst-Pat σ n P d (var (((n - 1) - r) + d)) b hσ
        (PE.trans (PE.cong (repeat liftSubst σ d) (plus-comm ((n - 1) - r) d))
          (PE.trans (substVar-lifts-≥ d σ ((n - 1) - r))
                    (PE.cong (wk1^ d) (hv 0 (leS le0)))))

  -- Instantiating the conclusion.
  subst-concl : ∀ σ i j P n (as : List Term) → n PE.≡ length as →
    (∀ x → σ (n + x) PE.≡ var x) →
    (∀ q → q << n → subst σ (var ((n - 1) - q)) PE.≡ lookupDefault (var 0) as q) →
    subst (repeat liftSubst σ n) (concl i j P n) PE.≡ wk1^ n (P [ ctr i j as ])
  subst-concl σ i j P n as n≡ hσ hv =
    subst-Pat σ n P n (ctr i j (ctrVars n)) (ctr i j as) hσ
      (PE.trans (subst-ctr (repeat liftSubst σ n) i j (ctrVars n))
        (PE.trans
          (PE.cong (ctr i j)
            (PE.trans (map-map (subst (repeat liftSubst σ n))
                               (λ v → var (((n + n) - 1) - v)) (range n))
              varsEq))
          (PE.sym (wk1^-ctr n i j as))))
    where
    varsEq : map (λ v → subst (repeat liftSubst σ n) (var (((n + n) - 1) - v))) (range n)
             PE.≡ map (wk1^ n) as
    varsEq =
      PE.trans
        (PE.cong (λ m → map (λ v → subst (repeat liftSubst σ n) (var (((n + n) - 1) - v)))
                            (range m))
          (PE.trans n≡ (PE.sym (length-map (wk1^ n) as))))
        (map-range-≡ (var 0)
          (λ v → subst (repeat liftSubst σ n) (var (((n + n) - 1) - v)))
          (map (wk1^ n) as)
          (λ q hq →
            let hq′ : q << n
                hq′ = PE.subst (λ m → q << m)
                        (PE.trans (length-map (wk1^ n) as) (PE.sym n≡)) hq
            in PE.trans
                 (PE.cong (repeat liftSubst σ n) (varIdx n q hq′))
                 (PE.trans (substVar-lifts-≥ n σ ((n - 1) - q))
                   (PE.trans (PE.cong (wk1^ n) (hv q hq′))
                     (PE.sym (lookupDefault-map (wk1^ n) (var 0) (var 0) as q
                               (PE.subst (λ m → q << m) n≡ hq′)))))))

  -- The method body, with all n argument binders instantiated by as.
  instBody : ∀ i j P lG n (as : List Term) → n PE.≡ length as →
    subst (argSubst as) (foldr (Πih ! lG) (concl i j P n) (ihGo n P 0 (range n)))
    PE.≡ arrows lG (map (λ a → P [ a ]) as) (P [ ctr i j as ])
  instBody i j P lG n as n≡ =
    PE.trans
      (PE.trans
        (subst-foldr-Π (argSubst as) ! lG lG ! (concl i j P n) (ihGo n P 0 (range n)))
        (PE.cong₂ (foldr (Πih ! lG))
          (PE.trans
            (PE.cong (λ m → subst (repeat liftSubst (argSubst as) m) (concl i j P n))
              (PE.trans (length-ihGo n P 0 (range n)) (length-range n)))
            (subst-concl (argSubst as) i j P n as n≡ hσ hv))
          (subst-tel-inst (argSubst as) n P 0 (range n) as
            (PE.trans (length-range n) n≡) hσ
            (λ q hq →
              let hq′ : q << n
                  hq′ = PE.subst (λ m → q << m) (length-range n) hq
              in PE.trans (PE.cong (λ x → subst (argSubst as) (var ((n - 1) - x)))
                                   (lookup-range n q hq′))
                          (hv q hq′)))))
      (PE.trans
        (PE.cong (λ m → foldr (Πih ! lG) (wk1^ m (P [ ctr i j as ]))
                          (wkTele (map (λ a → P [ a ]) as)))
          (PE.trans n≡ (PE.sym (length-map (λ a → P [ a ]) as))))
        (arrows-foldr lG (map (λ a → P [ a ]) as) (P [ ctr i j as ])))
    where
    hσ : ∀ x → argSubst as (n + x) PE.≡ var x
    hσ x = PE.trans (PE.cong (λ m → argSubst as (m + x)) n≡) (argSubst-shift as x)

    hv : ∀ q → q << n → subst (argSubst as) (var ((n - 1) - q))
                        PE.≡ lookupDefault (var 0) as q
    hv q hq =
      PE.trans (PE.cong (λ m → subst (argSubst as) (var ((m - 1) - q))) n≡)
               (argSubst-var as q (PE.subst (λ m → q << m) n≡ hq))

------------------------------------------------------------------------
-- Reducible application of a method to the constructor arguments and to
-- the induction hypotheses.

private
  -- Argument phase: the domains are the closed type Ind i, so the
  -- telescope is peeled one binder at a time by appTerm / substSΠ₁.
  appsArg : ∀ {Δ i lG l Body t} ([Ind] : Δ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ]) {as : List Term}
          → All (λ a → Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]) as
          → ([T] : Δ ⊩⟨ l ⟩ foldr (Πarg ! lG) Body (replicate (length as) (Ind i))
                              ^ [ ! , ι lG ])
          → Δ ⊩⟨ l ⟩ t ∷ foldr (Πarg ! lG) Body (replicate (length as) (Ind i))
                        ^ [ ! , ι lG ] / [T]
          → ∃ λ ([R] : Δ ⊩⟨ l ⟩ subst (argSubst as) Body ^ [ ! , ι lG ])
              → Δ ⊩⟨ l ⟩ apps lG t as ∷ subst (argSubst as) Body ^ [ ! , ι lG ] / [R]
  appsArg {Body = Body} [Ind] []ₐ [T] [t] =
    let [R] = irrelevance′ (PE.sym (subst-id Body)) [T]
    in  [R] , irrelevanceTerm′ (PE.sym (subst-id Body)) PE.refl PE.refl [T] [R] [t]
  appsArg {i = i} {lG = lG} {Body = Body} [Ind] {as = a ∷ₗ as} ([a] ∷ₐ [as]) [T] [t] =
    let n     = length as
        Body′ = subst (repeat liftSubst (sgSubst a) n) Body
        eqB   = PE.trans (subst-foldr-Π-closed (sgSubst a) ! ⁰ lG ! Body
                            (replicate n (Ind i))
                            (λ σ' → subst-replicate-Ind σ' n i))
                  (PE.cong (λ m → foldr (Πarg ! lG)
                                    (subst (repeat liftSubst (sgSubst a) m) Body)
                                    (replicate n (Ind i)))
                           (length-replicate n (Ind i)))
        [Ta]  = substSΠ₁ [T] [Ind] [a]
        [Ta]′ = irrelevance′ eqB [Ta]
        [ta]  = irrelevanceTerm′ eqB PE.refl PE.refl [Ta] [Ta]′
                  (appTerm PE.refl [Ind] [Ta] [T] [t] [a])
        [R]′  = proj₁ (appsArg {Body = Body′} [Ind] [as] [Ta]′ [ta])
        [r]′  = proj₂ (appsArg {Body = Body′} [Ind] [as] [Ta]′ [ta])
        eqR   = substCompEq {σ = argSubst as} {σ′ = repeat liftSubst (sgSubst a) n} Body
        [R]   = irrelevance′ eqR [R]′
    in  [R] , irrelevanceTerm′ eqR PE.refl PE.refl [R]′ [R] [r]′

  -- Hypothesis phase: once the arguments are instantiated the remaining
  -- telescope is a chain of non-dependent arrows, peeled by wk1-singleSubst.
  appsIH : ∀ {Δ lG l E t} {Ds us : List Term}
         → All₂ (λ D u → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                           → Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D]) Ds us
         → ([T] : Δ ⊩⟨ l ⟩ arrows lG Ds E ^ [ ! , ι lG ])
         → Δ ⊩⟨ l ⟩ t ∷ arrows lG Ds E ^ [ ! , ι lG ] / [T]
         → ∃ λ ([E] : Δ ⊩⟨ l ⟩ E ^ [ ! , ι lG ])
             → Δ ⊩⟨ l ⟩ apps lG t us ∷ E ^ [ ! , ι lG ] / [E]
  appsIH []ₐ [T] [t] = [T] , [t]
  appsIH {lG = lG} {E = E} {Ds = D ∷ₗ Ds} {us = u ∷ₗ us} (([D] , [u]) ∷ₐ [us]) [T] [t] =
    let eqA   = wk1-singleSubst (arrows lG Ds E) u
        [Tu]  = substSΠ₁ [T] [D] [u]
        [Tu]′ = irrelevance′ eqA [Tu]
        [tu]  = irrelevanceTerm′ eqA PE.refl PE.refl [Tu] [Tu]′
                  (appTerm PE.refl [D] [Tu] [T] [t] [u])
    in  appsIH [us] [Tu]′ [tu]

  apps-++ : ∀ l t (xs ys : List Term) → apps l t (xs ++ ys) PE.≡ apps l (apps l t xs) ys
  apps-++ l t []ₗ ys = PE.refl
  apps-++ l t (x ∷ₗ xs) ys = apps-++ l (t ∘ x ^ l) xs ys

  -- The reduct of IndRect on a constructor: the j-th method applied to the
  -- constructor arguments and then to the induction hypotheses.
  appsMethod : ∀ {Δ i j Ts P lG l m args ihs}
    → ([Ind] : Δ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
    → (pos : All (SU.isPositive i) Ts)
    → (n≡ : ctrArity Ts PE.≡ length args)
    → All (λ a → Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]) args
    → ([T] : Δ ⊩⟨ l ⟩ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ])
    → Δ ⊩⟨ l ⟩ m ∷ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ] / [T]
    → All₂ (λ D u → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                      → Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
           (map (λ a → P [ a ]) args) ihs
    → ∃ λ ([E] : Δ ⊩⟨ l ⟩ (P [ ctr i j args ]) ^ [ ! , ι lG ])
        → Δ ⊩⟨ l ⟩ apps lG m (args ++ ihs) ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E]
  appsMethod {i = i} {j = j} {Ts = Ts} {P = P} {lG = lG} {m = m} {args = args} {ihs = ihs}
             [Ind] pos n≡ [args] [T] [m] [ihs] =
    let n     = ctrArity Ts
        Body₀ = foldr (Πih ! lG) (concl i j P n) (ihGo n P 0 (range n))
        eqT   = PE.trans (branchTy-nf i j Ts P ! lG pos)
                  (PE.cong (λ k → foldr (Πarg ! lG) Body₀ (replicate k (Ind i))) n≡)
        [T]′  = irrelevance′ eqT [T]
        [m]′  = irrelevanceTerm′ eqT PE.refl PE.refl [T] [T]′ [m]
        [R]   = proj₁ (appsArg [Ind] [args] [T]′ [m]′)
        [r]   = proj₂ (appsArg [Ind] [args] [T]′ [m]′)
        eqR   = instBody i j P lG n args n≡
        [R]′  = irrelevance′ eqR [R]
        [r]′  = irrelevanceTerm′ eqR PE.refl PE.refl [R] [R]′ [r]
        [E]   = proj₁ (appsIH [ihs] [R]′ [r]′)
        [e]   = proj₂ (appsIH [ihs] [R]′ [r]′)
    in  [E] , PE.subst (λ t → _ ⊩⟨ _ ⟩ t ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E])
                       (PE.sym (apps-++ lG m args ihs)) [e]

private
  -- Congruence counterparts of appsArg / appsIH / appsMethod.  Only the
  -- left-hand telescope is needed: app-congTerm peels the equality using
  -- the unprimed Π-type alone.
  appsArg-cong : ∀ {Δ i lG l Body t t′} ([Ind] : Δ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
               {as as′ : List Term}
             → All₂ (λ a a′ → (Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])
                            × (Δ ⊩⟨ l ⟩ a′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])
                            × (Δ ⊩⟨ l ⟩ a ≡ a′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])) as as′
             → ([T] : Δ ⊩⟨ l ⟩ foldr (Πarg ! lG) Body (replicate (length as) (Ind i))
                                 ^ [ ! , ι lG ])
             → Δ ⊩⟨ l ⟩ t ≡ t′ ∷ foldr (Πarg ! lG) Body (replicate (length as) (Ind i))
                           ^ [ ! , ι lG ] / [T]
             → ([R] : Δ ⊩⟨ l ⟩ subst (argSubst as) Body ^ [ ! , ι lG ])
             → Δ ⊩⟨ l ⟩ apps lG t as ≡ apps lG t′ as′ ∷ subst (argSubst as) Body
                           ^ [ ! , ι lG ] / [R]
  appsArg-cong {Body = Body} [Ind] []ₐ [T] [t≡t′] [R] =
    irrelevanceEqTerm′ (PE.sym (subst-id Body)) PE.refl PE.refl [T] [R] [t≡t′]
  appsArg-cong {i = i} {lG = lG} {Body = Body} [Ind] {as = a ∷ₗ as}
               (([a] , [a′] , [a≡a′]) ∷ₐ [aa]) [T] [t≡t′] [R] =
    let n     = length as
        Body′ = subst (repeat liftSubst (sgSubst a) n) Body
        eqB   = PE.trans (subst-foldr-Π-closed (sgSubst a) ! ⁰ lG ! Body
                            (replicate n (Ind i))
                            (λ σ' → subst-replicate-Ind σ' n i))
                  (PE.cong (λ m → foldr (Πarg ! lG)
                                    (subst (repeat liftSubst (sgSubst a) m) Body)
                                    (replicate n (Ind i)))
                           (length-replicate n (Ind i)))
        [Ta]  = substSΠ₁ [T] [Ind] [a]
        [Ta]′ = irrelevance′ eqB [Ta]
        [ta≡] = irrelevanceEqTerm′ eqB PE.refl PE.refl [Ta] [Ta]′
                  (app-congTerm [Ind] [Ta] [T] [t≡t′] [a] [a′] [a≡a′])
        eqR   = substCompEq {σ = argSubst as} {σ′ = repeat liftSubst (sgSubst a) n} Body
        [R]′  = irrelevance′ (PE.sym eqR) [R]
        rec   = appsArg-cong {Body = Body′} [Ind] [aa] [Ta]′ [ta≡] [R]′
    in  irrelevanceEqTerm′ eqR PE.refl PE.refl [R]′ [R] rec

  appsIH-cong : ∀ {Δ lG l E t t′} {Ds us us′ : List Term}
              → All₃ (λ D u u′ → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                                   → (Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
                                   × (Δ ⊩⟨ l ⟩ u′ ∷ D ^ [ ! , ι lG ] / [D])
                                   × (Δ ⊩⟨ l ⟩ u ≡ u′ ∷ D ^ [ ! , ι lG ] / [D]))
                     Ds us us′
              → ([T] : Δ ⊩⟨ l ⟩ arrows lG Ds E ^ [ ! , ι lG ])
              → Δ ⊩⟨ l ⟩ t ≡ t′ ∷ arrows lG Ds E ^ [ ! , ι lG ] / [T]
              → ([E] : Δ ⊩⟨ l ⟩ E ^ [ ! , ι lG ])
              → Δ ⊩⟨ l ⟩ apps lG t us ≡ apps lG t′ us′ ∷ E ^ [ ! , ι lG ] / [E]
  appsIH-cong []ₐ [T] [t≡t′] [E] = irrelevanceEqTerm [T] [E] [t≡t′]
  appsIH-cong {lG = lG} {E = E} {Ds = D ∷ₗ Ds} {us = u ∷ₗ us}
              (([D] , [u] , [u′] , [u≡u′]) ∷ₐ [us]) [T] [t≡t′] [E] =
    let eqA   = wk1-singleSubst (arrows lG Ds E) u
        [Tu]  = substSΠ₁ [T] [D] [u]
        [Tu]′ = irrelevance′ eqA [Tu]
        [tu≡] = irrelevanceEqTerm′ eqA PE.refl PE.refl [Tu] [Tu]′
                  (app-congTerm [D] [Tu] [T] [t≡t′] [u] [u′] [u≡u′])
    in  appsIH-cong [us] [Tu]′ [tu≡] [E]

  -- Projections out of the zipped congruence data.
  argFst : ∀ {Δ i l} ([Ind] : Δ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ]) {as as′ : List Term}
         → All₂ (λ a a′ → (Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])
                        × (Δ ⊩⟨ l ⟩ a′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])
                        × (Δ ⊩⟨ l ⟩ a ≡ a′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])) as as′
         → All (λ a → Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind]) as
  argFst [Ind] []ₐ = []ₐ
  argFst [Ind] (([a] , _ , _) ∷ₐ ps) = [a] ∷ₐ argFst [Ind] ps

  ihFst : ∀ {Δ lG l} {Ds us us′ : List Term}
        → All₃ (λ D u u′ → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                             → (Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
                             × (Δ ⊩⟨ l ⟩ u′ ∷ D ^ [ ! , ι lG ] / [D])
                             × (Δ ⊩⟨ l ⟩ u ≡ u′ ∷ D ^ [ ! , ι lG ] / [D]))
               Ds us us′
        → All₂ (λ D u → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                          → Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D]) Ds us
  ihFst []ₐ = []ₐ
  ihFst (([D] , [u] , _ , _) ∷ₐ ps) = ([D] , [u]) ∷ₐ ihFst ps

  lookupAll₃ : ∀ {A} {P : A → A → A → Set} {xs ys zs} (dx dy dz : A)
             → All₃ P xs ys zs → ∀ n → n << length xs
             → P (lookupDefault dx xs n) (lookupDefault dy ys n) (lookupDefault dz zs n)
  lookupAll₃ dx dy dz []ₐ n ()
  lookupAll₃ dx dy dz (p ∷ₐ _) 0 (leS _) = p
  lookupAll₃ dx dy dz (_ ∷ₐ ps) (1+ n) (leS h) = lookupAll₃ dx dy dz ps n h

  zipArgs : ∀ {Δ i} {as as′ : List Term}
          → All (λ a → Δ ⊩Ind a ∷Ind i) as
          → All (λ a → Δ ⊩Ind a ∷Ind i) as′
          → All₂ (λ a a′ → Δ ⊩Ind a ≡ a′ ∷Ind i) as as′
          → All₂ (λ a a′ → (Δ ⊩Ind a ∷Ind i) × (Δ ⊩Ind a′ ∷Ind i)
                         × (Δ ⊩Ind a ≡ a′ ∷Ind i)) as as′
  zipArgs []ₐ []ₐ []ₐ = []ₐ
  zipArgs ([a] ∷ₐ ps) ([a′] ∷ₐ ps′) ([e] ∷ₐ pps) =
    ([a] , [a′] , [e]) ∷ₐ zipArgs ps ps′ pps

  -- The β-reduct congruence: the j-th methods applied to the constructor
  -- arguments and then to the induction hypotheses.
  appsMethod-cong : ∀ {Δ i j Ts P lG l m m′ args args′ ihs ihs′}
    → ([Ind] : Δ ⊩⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ])
    → (pos : All (SU.isPositive i) Ts)
    → (n≡ : ctrArity Ts PE.≡ length args)
    → All₂ (λ a a′ → (Δ ⊩⟨ l ⟩ a ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])
                   × (Δ ⊩⟨ l ⟩ a′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])
                   × (Δ ⊩⟨ l ⟩ a ≡ a′ ∷ Ind i ^ [ ! , ι ⁰ ] / [Ind])) args args′
    → ([T] : Δ ⊩⟨ l ⟩ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ])
    → Δ ⊩⟨ l ⟩ m ∷ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ] / [T]
    → Δ ⊩⟨ l ⟩ m ≡ m′ ∷ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ] / [T]
    → All₃ (λ D u u′ → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                         → (Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u′ ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u ≡ u′ ∷ D ^ [ ! , ι lG ] / [D]))
           (map (λ a → P [ a ]) args) ihs ihs′
    → ([E] : Δ ⊩⟨ l ⟩ (P [ ctr i j args ]) ^ [ ! , ι lG ])
    → Δ ⊩⟨ l ⟩ apps lG m (args ++ ihs) ≡ apps lG m′ (args′ ++ ihs′)
                  ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E]
  appsMethod-cong {i = i} {j = j} {Ts = Ts} {P = P} {lG = lG} {m = m} {m′ = m′}
                  {args = args} {args′ = args′} {ihs = ihs} {ihs′ = ihs′}
                  [Ind] pos n≡ [aa] [T] [m] [m≡m′] [ihs] [E] =
    let n      = ctrArity Ts
        Body₀  = foldr (Πih ! lG) (concl i j P n) (ihGo n P 0 (range n))
        eqT    = PE.trans (branchTy-nf i j Ts P ! lG pos)
                   (PE.cong (λ k → foldr (Πarg ! lG) Body₀ (replicate k (Ind i))) n≡)
        [T]′   = irrelevance′ eqT [T]
        [m]′   = irrelevanceTerm′ eqT PE.refl PE.refl [T] [T]′ [m]
        [m≡]′  = irrelevanceEqTerm′ eqT PE.refl PE.refl [T] [T]′ [m≡m′]
        [R]    = proj₁ (appsArg [Ind] (argFst [Ind] [aa]) [T]′ [m]′)
        eqR    = instBody i j P lG n args n≡
        [R]′   = irrelevance′ eqR [R]
        [ar≡]  = appsArg-cong [Ind] [aa] [T]′ [m≡]′ [R]
        [ar≡]′ = irrelevanceEqTerm′ eqR PE.refl PE.refl [R] [R]′ [ar≡]
        [ih≡]  = appsIH-cong [ihs] [R]′ [ar≡]′ [E]
    in  PE.subst (λ x → _ ⊩⟨ _ ⟩ x ≡ apps lG m′ (args′ ++ ihs′)
                          ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E])
          (PE.sym (apps-++ lG m args ihs))
          (PE.subst (λ y → _ ⊩⟨ _ ⟩ apps lG (apps lG m args) ihs ≡ y
                             ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E])
             (PE.sym (apps-++ lG m′ args′ ihs′)) [ih≡])

-- The motive P is a term, so its instantiation needs no context
-- extension: everything below lives in the ambient Δ.

private
  ⊢All-length : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → length ts PE.≡ length As
  ⊢All-length εⱼ = PE.refl
  ⊢All-length (consⱼ _ rest) = PE.cong 1+ (⊢All-length rest)

mutual
  IndRectTerm : ∀ {Δ ind P rG lG ms t l}
    (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
    (⊢Δ : ⊢ Δ)
    (ind∈ : ind ∈ₗ senv)
    ([P∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P ^ [ rG , ι lG ])
    ([Pu] : ∀ {u} → Δ ⊩Ind u ∷Ind SU.SInd.name ind → Δ ⊩⟨ l ⟩ P [ u ] ^ [ rG , ι lG ])
    ([Pu≡] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
               ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
             → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
             → Δ ⊩⟨ l ⟩ P [ u ] ≡ P [ u′ ] ^ [ rG , ι lG ] / [Pu] [u])
    (⊢ms : Δ ⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ])
    ([ms] : All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                            → Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                 (indRectBranchTyList ind P rG lG) ms)
    ([t] : Δ ⊩Ind t ∷Ind SU.SInd.name ind)
    → Δ ⊩⟨ l ⟩ IndRect (SU.SInd.name ind) lG P t ms ∷ P [ t ] ^ [ rG , ι lG ] / [Pu] [t]
  IndRectTerm {ind = ind} {rG = %} {l = l} rGlG ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] [t] =
    let [Ind] = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ)))
    in  logRelIrr ([Pu] [t])
                  (IndRectⱼ rGlG ind∈ (escape [P∙]) (escapeTerm [Ind] [t]) ⊢ms)
  IndRectTerm {ind = ind} {P = P} {rG = !} {lG = lG} {ms = ms} {l = l}
              rGlG ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms]
              (Indₜ k d k≡k (ne (neNfₜ neK ⊢k k~k))) =
    let [Ind]   = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ)))
        [t]     = Indₜ k d k≡k (ne (neNfₜ neK ⊢k k~k))
        ⊢P      = escape [P∙]
        ⊢P≅P    = escapeEq [P∙] (reflEq [P∙])
        [k]     = neuTerm [Ind] neK ⊢k k~k
        [t≡k]   = proj₂ (redSubst*Term (redₜ d) [Ind] [k])
        [Pt]    = [Pu] [t]
        [Pk]    = [Pu] [k]
        [Pt≡Pk] = [Pu≡] [t] [k] [t≡k]
        IndRectK = neuTerm [Pk] (IndRectₙ neK) (IndRectⱼ rGlG ind∈ ⊢P ⊢k ⊢ms)
                           (~-IndRect ind∈ ⊢P≅P k~k (reflAllEq′ ⊢ms))
        reduction = IndRect-subst* ind∈ ⊢P (redₜ d) ⊢ms [Ind] [k]
                      (λ [u] [u′] [u≡u′] →
                         ≅-eq (escapeEq ([Pu] [u]) ([Pu≡] [u] [u′] [u≡u′])))
    in  proj₁ (redSubst*Term reduction [Pt]
                 (convTerm₂ [Pt] [Pk] [Pt≡Pk] IndRectK))
  IndRectTerm {ind = ind} {P = P} {rG = !} {lG = lG} {ms = ms}
              rGlG ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms]
              (Indₜ .(ctr (SU.SInd.name ind) j args) d k≡k (ctrᵣ {j} {args} ps))
    with inversion-Ctr (_⊢_:⇒*:_∷_^_.⊢u d)
  ... | ind′ , Ts , ind∈′ , name≡ , eq , ⊢args
    with SU.name-inj senv (proj₁ swf) ind∈′ ind∈ name≡
  ... | PE.refl =
    let i       = SU.SInd.name ind
        [Ind]   = Indᵣ (idRed:*: (univ (Indⱼ ⊢Δ)))
        [t]     = Indₜ (ctr i j args) d k≡k (ctrᵣ ps)
        ⊢P      = escape [P∙]
        ⊢ctr    = _⊢_:⇒*:_∷_^_.⊢u d
        pos     = all∈ (SU.ctrArgsTypesPositive ind j Ts eq)
        n≡      = PE.sym (PE.trans (⊢All-length ⊢args)
                           (length-map emb-stype Ts))
        [k]     = Indₜ (ctr i j args) (idRedTerm:*: ⊢ctr) k≡k (ctrᵣ ps)
        [t≡k]   = proj₂ (redSubst*Term (redₜ d) [Ind] [k])
        [Pt]    = [Pu] [t]
        [Pk]    = [Pu] [k]
        [Pt≡Pk] = [Pu≡] [t] [k] [t≡k]
        nthTy   = nth-map (λ jTs → indRectBranchTy i (proj₁ jTs) (proj₂ jTs) P ! lG)
                    (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) j
                    (nth-zip-range (SU.SInd.ctrArgsTypes ind) j eq)
        nthms   = nth-lookupDefault (ctr i j args) ms j
                    (PE.subst (λ n → j << n) (All₂-length [ms])
                      (nth-length (indRectBranchTyList ind P ! lG) j nthTy))
        [Tⱼ]    = proj₁ (nthAll₂ [ms] j nthTy nthms)
        [mⱼ]    = proj₂ (nthAll₂ [ms] j nthTy nthms)
        [ihs]   = IndRectTerms ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] ps
        [E]     = proj₁ (appsMethod {j = j} {P = P} [Ind] pos n≡ ps [Tⱼ] [mⱼ] [ihs])
        [e]     = proj₂ (appsMethod {j = j} {P = P} [Ind] pos n≡ ps [Tⱼ] [mⱼ] [ihs])
        [e]′    = irrelevanceTerm [E] [Pk] [e]
        reduction = IndRect-subst* ind∈ ⊢P (redₜ d) ⊢ms [Ind] [k]
                      (λ [u] [u′] [u≡u′] →
                         ≅-eq (escapeEq ([Pu] [u]) ([Pu≡] [u] [u′] [u≡u′])))
                    ⇨∷* (conv* (IndRect-ctr ind∈ eq ⊢P ⊢args ⊢ms nthms
                                ⇨ id (escapeTerm [Pk] [e]′))
                               (sym (≅-eq (escapeEq [Pt] [Pt≡Pk]))))
    in  proj₁ (redSubst*Term reduction [Pt]
                 (convTerm₂ [Pt] [Pk] [Pt≡Pk] [e]′))

  -- The induction hypotheses: IndRect applied to each constructor argument.
  IndRectTerms : ∀ {Δ ind P lG ms l} {args : List Term}
    (⊢Δ : ⊢ Δ)
    (ind∈ : ind ∈ₗ senv)
    ([P∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P ^ [ ! , ι lG ])
    ([Pu] : ∀ {u} → Δ ⊩Ind u ∷Ind SU.SInd.name ind → Δ ⊩⟨ l ⟩ P [ u ] ^ [ ! , ι lG ])
    ([Pu≡] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
               ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
             → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
             → Δ ⊩⟨ l ⟩ P [ u ] ≡ P [ u′ ] ^ [ ! , ι lG ] / [Pu] [u])
    (⊢ms : Δ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ])
    ([ms] : All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι lG ])
                            → Δ ⊩⟨ l ⟩ m ∷ A ^ [ ! , ι lG ] / [A])
                 (indRectBranchTyList ind P ! lG) ms)
    → All (λ a → Δ ⊩Ind a ∷Ind SU.SInd.name ind) args
    → All₂ (λ D u → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                      → Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
           (map (λ a → P [ a ]) args)
           (map (λ a → IndRect (SU.SInd.name ind) lG P a ms) args)
  IndRectTerms ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] []ₐ = []ₐ
  IndRectTerms ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] (p ∷ₐ rest) =
    ([Pu] p , IndRectTerm (λ ()) ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] p)
    ∷ₐ IndRectTerms ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] rest

  IndRect-congTerm : ∀ {Δ ind P P′ rG lG ms ms′ t t′ l}
    (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
    (⊢Δ : ⊢ Δ)
    (ind∈ : ind ∈ₗ senv)
    ([P∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P ^ [ rG , ι lG ])
    ([P′∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P′ ^ [ rG , ι lG ])
    ([P≡P′∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P ≡ P′ ^ [ rG , ι lG ] / [P∙])
    ([Pu] : ∀ {u} → Δ ⊩Ind u ∷Ind SU.SInd.name ind → Δ ⊩⟨ l ⟩ P [ u ] ^ [ rG , ι lG ])
    ([Pu≡] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
               ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
             → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
             → Δ ⊩⟨ l ⟩ P [ u ] ≡ P [ u′ ] ^ [ rG , ι lG ] / [Pu] [u])
    ([P′u] : ∀ {u} → Δ ⊩Ind u ∷Ind SU.SInd.name ind → Δ ⊩⟨ l ⟩ P′ [ u ] ^ [ rG , ι lG ])
    ([P′u≡] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
                ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
              → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
              → Δ ⊩⟨ l ⟩ P′ [ u ] ≡ P′ [ u′ ] ^ [ rG , ι lG ] / [P′u] [u])
    ([PP′u] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
                ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
              → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
              → Δ ⊩⟨ l ⟩ P [ u ] ≡ P′ [ u′ ] ^ [ rG , ι lG ] / [Pu] [u])
    (⊢ms : Δ ⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ])
    (⊢ms′ : Δ ⊢All ms′ ∷ indRectBranchTyList ind P′ rG lG ^ [ rG , ι lG ])
    (⊢ms≡ : Δ ⊢All ms ≡ ms′ ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ])
    ([ms′] : All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                             → Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                  (indRectBranchTyList ind P′ rG lG) ms′)
    ([ms≡] : All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                                → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                                × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                                × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A]))
                  (indRectBranchTyList ind P rG lG) ms ms′)
    ([t] : Δ ⊩Ind t ∷Ind SU.SInd.name ind)
    ([t′] : Δ ⊩Ind t′ ∷Ind SU.SInd.name ind)
    ([t≡t′] : Δ ⊩Ind t ≡ t′ ∷Ind SU.SInd.name ind)
    → Δ ⊩⟨ l ⟩ IndRect (SU.SInd.name ind) lG P t ms ≡ IndRect (SU.SInd.name ind) lG P′ t′ ms′
                  ∷ P [ t ] ^ [ rG , ι lG ] / [Pu] [t]
  IndRect-congTerm {ind = ind} {rG = %} {l = l} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡] [t] [t′] [t≡t′] =
    let [Ind]      = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ)))
        [Pt]       = [Pu] [t]
        [Pt≡P′t′]  = [PP′u] [t] [t′] [t≡t′]
    in  logRelIrrEq [Pt]
          (IndRectⱼ rGlG ind∈ (escape [P∙]) (escapeTerm [Ind] [t]) ⊢ms)
          (conv (IndRectⱼ rGlG ind∈ (escape [P′∙]) (escapeTerm [Ind] [t′]) ⊢ms′)
                (sym (≅-eq (escapeEq [Pt] [Pt≡P′t′]))))
  IndRect-congTerm {ind = ind} {P = P} {P′ = P′} {rG = !} {lG = lG} {ms = ms} {ms′ = ms′} {l = l}
                   rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   (Indₜ k d k≡k (ne (neNfₜ neK ⊢k k~k)))
                   (Indₜ k′ d′ k′≡k′ (ne (neNfₜ neK′ ⊢k′ k′~k′)))
                   (Indₜ₌ k₁ k₁′ d₁ d₁′ k₁≡k₁′ (ne (neNfₜ₌ neK₁ neK₁′ k₁~k₁′))) =
    let k₁≡k        = whrDet*Term (redₜ d₁ , ne neK₁) (redₜ d , ne neK)
        k₁′≡k′      = whrDet*Term (redₜ d₁′ , ne neK₁′) (redₜ d′ , ne neK′)
        [Ind]       = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ)))
        [t]         = Indₜ k d k≡k (ne (neNfₜ neK ⊢k k~k))
        [t′]        = Indₜ k′ d′ k′≡k′ (ne (neNfₜ neK′ ⊢k′ k′~k′))
        [t≡t′]      = Indₜ₌ k₁ k₁′ d₁ d₁′ k₁≡k₁′ (ne (neNfₜ₌ neK₁ neK₁′ k₁~k₁′))
        ⊢P          = escape [P∙]
        ⊢P′         = escape [P′∙]
        ⊢P≅P        = escapeEq [P∙] (reflEq [P∙])
        ⊢P′≅P′      = escapeEq [P′∙] (reflEq [P′∙])
        ⊢P≅P′       = escapeEq [P∙] [P≡P′∙]
        [k]         = neuTerm [Ind] neK ⊢k k~k
        [k′]        = neuTerm [Ind] neK′ ⊢k′ k′~k′
        [t≡k]       = proj₂ (redSubst*Term (redₜ d) [Ind] [k])
        [t′≡k′]     = proj₂ (redSubst*Term (redₜ d′) [Ind] [k′])
        [k≡k′]      = transEqTerm [Ind] (symEqTerm [Ind] [t≡k])
                        (transEqTerm [Ind] [t≡t′] [t′≡k′])
        [Pt]        = [Pu] [t]
        [Pk]        = [Pu] [k]
        [P′t′]      = [P′u] [t′]
        [P′k′]      = [P′u] [k′]
        [Pt≡Pk]     = [Pu≡] [t] [k] [t≡k]
        [P′t′≡P′k′] = [P′u≡] [t′] [k′] [t′≡k′]
        [Pt≡P′t′]   = [PP′u] [t] [t′] [t≡t′]
        [Pk≡P′k′]   = [PP′u] [k] [k′] [k≡k′]
        IndRectK    = neuTerm [Pk] (IndRectₙ neK) (IndRectⱼ rGlG ind∈ ⊢P ⊢k ⊢ms)
                              (~-IndRect ind∈ ⊢P≅P k~k (reflAllEq′ ⊢ms))
        IndRectK′   = neuTerm [P′k′] (IndRectₙ neK′) (IndRectⱼ rGlG ind∈ ⊢P′ ⊢k′ ⊢ms′)
                              (~-IndRect ind∈ ⊢P′≅P′ k′~k′ (reflAllEq′ ⊢ms′))
        IndRectK≡K′ = convEqTerm₂ [Pt] [Pk] [Pt≡Pk]
                        (neuEqTerm [Pk] (IndRectₙ neK) (IndRectₙ neK′)
                          (IndRectⱼ rGlG ind∈ ⊢P ⊢k ⊢ms)
                          (conv (IndRectⱼ rGlG ind∈ ⊢P′ ⊢k′ ⊢ms′)
                                (sym (≅-eq (escapeEq [Pk] [Pk≡P′k′]))))
                          (~-IndRect ind∈ ⊢P≅P′
                            (PE.subst₂ (λ x y → _ ⊢ x ~ y ∷ _ ^ [ ! , ι ⁰ ])
                                       k₁≡k k₁′≡k′ k₁~k₁′)
                            ⊢ms≡))
        reduction₁  = IndRect-subst* ind∈ ⊢P (redₜ d) ⊢ms [Ind] [k]
                        (λ [u] [u′] [u≡u′] →
                           ≅-eq (escapeEq ([Pu] [u]) ([Pu≡] [u] [u′] [u≡u′])))
        reduction₂  = IndRect-subst* ind∈ ⊢P′ (redₜ d′) ⊢ms′ [Ind] [k′]
                        (λ [u] [u′] [u≡u′] →
                           ≅-eq (escapeEq ([P′u] [u]) ([P′u≡] [u] [u′] [u≡u′])))
        eq₁ = proj₂ (redSubst*Term reduction₁ [Pt]
                       (convTerm₂ [Pt] [Pk] [Pt≡Pk] IndRectK))
        eq₂ = proj₂ (redSubst*Term reduction₂ [P′t′]
                       (convTerm₂ [P′t′] [P′k′] [P′t′≡P′k′] IndRectK′))
    in  transEqTerm [Pt] eq₁
          (transEqTerm [Pt] IndRectK≡K′
            (convEqTerm₂ [Pt] [P′t′] [Pt≡P′t′] (symEqTerm [P′t′] eq₂)))
  IndRect-congTerm {ind = ind} {P = P} {P′ = P′} {rG = !} {lG = lG} {ms = ms} {ms′ = ms′}
                   rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   (Indₜ .(ctr (SU.SInd.name ind) j args) d k≡k (ctrᵣ {j} {args} ps))
                   (Indₜ .(ctr (SU.SInd.name ind) j′ args′) d′ k′≡k′ (ctrᵣ {j′} {args′} ps′))
                   (Indₜ₌ .(ctr (SU.SInd.name ind) j₂ a₂) .(ctr (SU.SInd.name ind) j₂ a₂′)
                          d₁ d₁′ k₁≡k₁′ (ctrᵣ {j₂} {a₂} {a₂′} aa))
    with ctr-PE-injectivity (whrDet*Term (redₜ d₁ , ctrₙ) (redₜ d , ctrₙ))
  ... | _ , PE.refl , PE.refl
    with ctr-PE-injectivity (whrDet*Term (redₜ d₁′ , ctrₙ) (redₜ d′ , ctrₙ))
  ... | _ , PE.refl , PE.refl
    with inversion-Ctr (_⊢_:⇒*:_∷_^_.⊢u d) | inversion-Ctr (_⊢_:⇒*:_∷_^_.⊢u d′)
  ... | ind₁ , Ts , ind∈₁ , name≡₁ , eq , ⊢args
      | ind₂ , Ts′ , ind∈₂ , name≡₂ , eq′ , ⊢args′
    with SU.name-inj senv (proj₁ swf) ind∈₁ ind∈ name≡₁
       | SU.name-inj senv (proj₁ swf) ind∈₂ ind∈ name≡₂
  ... | PE.refl | PE.refl
    with PE.trans (PE.sym eq) eq′
  ... | PE.refl =
    let i           = SU.SInd.name ind
        [Ind]       = Indᵣ (idRed:*: (univ (Indⱼ ⊢Δ)))
        [ms]        = ihFst [ms≡]
        [t]         = Indₜ (ctr i j args) d k≡k (ctrᵣ ps)
        [t′]        = Indₜ (ctr i j args′) d′ k′≡k′ (ctrᵣ ps′)
        [t≡t′]      = Indₜ₌ (ctr i j args) (ctr i j args′) d₁ d₁′ k₁≡k₁′ (ctrᵣ aa)
        ⊢P          = escape [P∙]
        ⊢P′         = escape [P′∙]
        ⊢ctr        = _⊢_:⇒*:_∷_^_.⊢u d
        ⊢ctr′       = _⊢_:⇒*:_∷_^_.⊢u d′
        pos         = all∈ (SU.ctrArgsTypesPositive ind j Ts eq)
        n≡          = PE.sym (PE.trans (⊢All-length ⊢args)
                               (length-map emb-stype Ts))
        n≡′         = PE.sym (PE.trans (⊢All-length ⊢args′)
                               (length-map emb-stype Ts))
        [k]         = Indₜ (ctr i j args) (idRedTerm:*: ⊢ctr) k≡k (ctrᵣ ps)
        [k′]        = Indₜ (ctr i j args′) (idRedTerm:*: ⊢ctr′) k′≡k′ (ctrᵣ ps′)
        [t≡k]       = proj₂ (redSubst*Term (redₜ d) [Ind] [k])
        [t′≡k′]     = proj₂ (redSubst*Term (redₜ d′) [Ind] [k′])
        [k≡k′]      = transEqTerm [Ind] (symEqTerm [Ind] [t≡k])
                        (transEqTerm [Ind] [t≡t′] [t′≡k′])
        [Pt]        = [Pu] [t]
        [Pk]        = [Pu] [k]
        [P′t′]      = [P′u] [t′]
        [P′k′]      = [P′u] [k′]
        [Pt≡Pk]     = [Pu≡] [t] [k] [t≡k]
        [P′t′≡P′k′] = [P′u≡] [t′] [k′] [t′≡k′]
        [Pt≡P′t′]   = [PP′u] [t] [t′] [t≡t′]
        jTs         = nth-zip-range (SU.SInd.ctrArgsTypes ind) j eq
        nthTy       = nth-map (λ jTs′ → indRectBranchTy i (proj₁ jTs′) (proj₂ jTs′) P ! lG)
                        (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) j jTs
        nthTy′      = nth-map (λ jTs′ → indRectBranchTy i (proj₁ jTs′) (proj₂ jTs′) P′ ! lG)
                        (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) j jTs
        nthms       = nth-lookupDefault (ctr i j args) ms j
                        (PE.subst (λ n → j << n) (All₂-length [ms])
                          (nth-length (indRectBranchTyList ind P ! lG) j nthTy))
        nthms′      = nth-lookupDefault (ctr i j args′) ms′ j
                        (PE.subst (λ n → j << n) (All₂-length [ms′])
                          (nth-length (indRectBranchTyList ind P′ ! lG) j nthTy′))
        mⱼ≡         = nthAll₃ [ms≡] j nthTy nthms nthms′
        [Tⱼ]        = proj₁ mⱼ≡
        [mⱼ]        = proj₁ (proj₂ mⱼ≡)
        [mⱼ≡m′ⱼ]    = proj₂ (proj₂ (proj₂ mⱼ≡))
        [T′ⱼ]       = proj₁ (nthAll₂ [ms′] j nthTy′ nthms′)
        [m′ⱼ]       = proj₂ (nthAll₂ [ms′] j nthTy′ nthms′)
        [ihs]       = IndRectTerms ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] ps
        [ihs′]      = IndRectTerms ⊢Δ ind∈ [P′∙] [P′u] [P′u≡] ⊢ms′ [ms′] ps′
        [ihs≡]      = IndRect-congTerms ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡]
                        [PP′u] ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡] ps ps′ aa
        [E]         = proj₁ (appsMethod {j = j} {P = P} [Ind] pos n≡ ps [Tⱼ] [mⱼ] [ihs])
        [e]′        = irrelevanceTerm [E] [Pk]
                        (proj₂ (appsMethod {j = j} {P = P} [Ind] pos n≡ ps [Tⱼ] [mⱼ] [ihs]))
        [E′]        = proj₁ (appsMethod {j = j} {P = P′} [Ind] pos n≡′ ps′ [T′ⱼ] [m′ⱼ] [ihs′])
        [e′]′       = irrelevanceTerm [E′] [P′k′]
                        (proj₂ (appsMethod {j = j} {P = P′} [Ind] pos n≡′ ps′ [T′ⱼ] [m′ⱼ] [ihs′]))
        [e≡e′]      = convEqTerm₂ [Pt] [Pk] [Pt≡Pk]
                        (appsMethod-cong {j = j} {P = P} [Ind] pos n≡ (zipArgs ps ps′ aa)
                          [Tⱼ] [mⱼ] [mⱼ≡m′ⱼ] [ihs≡] [Pk])
        reduction₁  = IndRect-subst* ind∈ ⊢P (redₜ d) ⊢ms [Ind] [k]
                        (λ [u] [u′] [u≡u′] →
                           ≅-eq (escapeEq ([Pu] [u]) ([Pu≡] [u] [u′] [u≡u′])))
                      ⇨∷* (conv* (IndRect-ctr ind∈ eq ⊢P ⊢args ⊢ms nthms
                                  ⇨ id (escapeTerm [Pk] [e]′))
                                 (sym (≅-eq (escapeEq [Pt] [Pt≡Pk]))))
        reduction₂  = IndRect-subst* ind∈ ⊢P′ (redₜ d′) ⊢ms′ [Ind] [k′]
                        (λ [u] [u′] [u≡u′] →
                           ≅-eq (escapeEq ([P′u] [u]) ([P′u≡] [u] [u′] [u≡u′])))
                      ⇨∷* (conv* (IndRect-ctr ind∈ eq′ ⊢P′ ⊢args′ ⊢ms′ nthms′
                                  ⇨ id (escapeTerm [P′k′] [e′]′))
                                 (sym (≅-eq (escapeEq [P′t′] [P′t′≡P′k′]))))
        eq₁ = proj₂ (redSubst*Term reduction₁ [Pt]
                       (convTerm₂ [Pt] [Pk] [Pt≡Pk] [e]′))
        eq₂ = proj₂ (redSubst*Term reduction₂ [P′t′]
                       (convTerm₂ [P′t′] [P′k′] [P′t′≡P′k′] [e′]′))
    in  transEqTerm [Pt] eq₁
          (transEqTerm [Pt] [e≡e′]
            (convEqTerm₂ [Pt] [P′t′] [Pt≡P′t′] (symEqTerm [P′t′] eq₂)))
  -- Mismatching whnf shapes are impossible.
  IndRect-congTerm {rG = !} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   (Indₜ _ d _ (ctrᵣ _)) _
                   (Indₜ₌ _ _ d₁ _ _ (ne (neNfₜ₌ neK₁ _ _))) =
    ⊥-elim (ctr≢ne neK₁ (whrDet*Term (redₜ d , ctrₙ) (redₜ d₁ , ne neK₁)))
  IndRect-congTerm {rG = !} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   _ (Indₜ _ d′ _ (ctrᵣ _))
                   (Indₜ₌ _ _ _ d₁′ _ (ne (neNfₜ₌ _ neK₁′ _))) =
    ⊥-elim (ctr≢ne neK₁′ (whrDet*Term (redₜ d′ , ctrₙ) (redₜ d₁′ , ne neK₁′)))
  IndRect-congTerm {rG = !} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   (Indₜ _ d _ (ne (neNfₜ neK _ _))) _
                   (Indₜ₌ _ _ d₁ _ _ (ctrᵣ _)) =
    ⊥-elim (ctr≢ne neK (whrDet*Term (redₜ d₁ , ctrₙ) (redₜ d , ne neK)))
  IndRect-congTerm {rG = !} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   _ (Indₜ _ d′ _ (ne (neNfₜ neK′ _ _)))
                   (Indₜ₌ _ _ _ d₁′ _ (ctrᵣ _)) =
    ⊥-elim (ctr≢ne neK′ (whrDet*Term (redₜ d₁′ , ctrₙ) (redₜ d′ , ne neK′)))

  -- Congruence of the induction hypotheses.
  IndRect-congTerms : ∀ {Δ ind P P′ lG ms ms′ l} {args args′ : List Term}
    (⊢Δ : ⊢ Δ)
    (ind∈ : ind ∈ₗ senv)
    ([P∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P ^ [ ! , ι lG ])
    ([P′∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P′ ^ [ ! , ι lG ])
    ([P≡P′∙] : Δ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ P ≡ P′ ^ [ ! , ι lG ] / [P∙])
    ([Pu] : ∀ {u} → Δ ⊩Ind u ∷Ind SU.SInd.name ind → Δ ⊩⟨ l ⟩ P [ u ] ^ [ ! , ι lG ])
    ([Pu≡] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
               ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
             → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
             → Δ ⊩⟨ l ⟩ P [ u ] ≡ P [ u′ ] ^ [ ! , ι lG ] / [Pu] [u])
    ([P′u] : ∀ {u} → Δ ⊩Ind u ∷Ind SU.SInd.name ind → Δ ⊩⟨ l ⟩ P′ [ u ] ^ [ ! , ι lG ])
    ([P′u≡] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
                ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
              → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
              → Δ ⊩⟨ l ⟩ P′ [ u ] ≡ P′ [ u′ ] ^ [ ! , ι lG ] / [P′u] [u])
    ([PP′u] : ∀ {u u′} ([u] : Δ ⊩Ind u ∷Ind SU.SInd.name ind)
                ([u′] : Δ ⊩Ind u′ ∷Ind SU.SInd.name ind)
              → Δ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
              → Δ ⊩⟨ l ⟩ P [ u ] ≡ P′ [ u′ ] ^ [ ! , ι lG ] / [Pu] [u])
    (⊢ms : Δ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ])
    (⊢ms′ : Δ ⊢All ms′ ∷ indRectBranchTyList ind P′ ! lG ^ [ ! , ι lG ])
    (⊢ms≡ : Δ ⊢All ms ≡ ms′ ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ])
    ([ms′] : All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι lG ])
                             → Δ ⊩⟨ l ⟩ m ∷ A ^ [ ! , ι lG ] / [A])
                  (indRectBranchTyList ind P′ ! lG) ms′)
    ([ms≡] : All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι lG ])
                                → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ ! , ι lG ] / [A])
                                × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ ! , ι lG ] / [A])
                                × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ ! , ι lG ] / [A]))
                  (indRectBranchTyList ind P ! lG) ms ms′)
    → All (λ a → Δ ⊩Ind a ∷Ind SU.SInd.name ind) args
    → All (λ a → Δ ⊩Ind a ∷Ind SU.SInd.name ind) args′
    → All₂ (λ a a′ → Δ ⊩Ind a ≡ a′ ∷Ind SU.SInd.name ind) args args′
    → All₃ (λ D u u′ → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                         → (Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u′ ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u ≡ u′ ∷ D ^ [ ! , ι lG ] / [D]))
           (map (λ a → P [ a ]) args)
           (map (λ a → IndRect (SU.SInd.name ind) lG P a ms) args)
           (map (λ a → IndRect (SU.SInd.name ind) lG P′ a ms′) args′)
  IndRect-congTerms ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                    ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡] []ₐ []ₐ []ₐ = []ₐ
  IndRect-congTerms ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                    ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                    ([a] ∷ₐ ps) ([a′] ∷ₐ ps′) ([a≡a′] ∷ₐ pps) =
    let [D]      = [Pu] [a]
        [D′]     = [P′u] [a′]
        [D≡D′]   = [PP′u] [a] [a′] [a≡a′]
        [u]      = IndRectTerm (λ ()) ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms (ihFst [ms≡]) [a]
        [u′]     = convTerm₂ [D] [D′] [D≡D′]
                     (IndRectTerm (λ ()) ⊢Δ ind∈ [P′∙] [P′u] [P′u≡] ⊢ms′ [ms′] [a′])
        [u≡u′]   = IndRect-congTerm (λ ()) ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙]
                     [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                     ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡] [a] [a′] [a≡a′]
    in  ([D] , [u] , [u′] , [u≡u′])
        ∷ₐ IndRect-congTerms ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
             ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡] ps ps′ pps

private
  -- Reducible methods at a substitution (reducible counterpart of escapeMethodsσ).
  methodsσ : ∀ {Γ Δ σ ind P rG lG ms l}
    → ([Γ] : ⊩ᵛ Γ)
    → (⊢Δ : ⊢ Δ)
    → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
    → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                      → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
           ms (indRectBranchTyList ind P rG lG)
    → All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                      → Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
           (indRectBranchTyList ind (subst (liftSubst σ) P) rG lG) (map (subst σ) ms)
  methodsσ {Δ = Δ} {σ = σ} {ind = ind} {P = P} {rG = rG} {lG = lG} {ms = ms} {l = l}
           [Γ] ⊢Δ [σ] [ms] =
    PE.subst (λ As → All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                                     → Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                          As (map (subst σ) ms))
             (subst-indRectBranchTyList σ ind P rG lG)
             (go ms (indRectBranchTyList ind P rG lG) [ms])
    where
      go : ∀ ms′ As →
        All₂ (λ m A → ∃ λ ([A] : _ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / _)
                        → _ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / _ / [A]) ms′ As
        → All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                          → Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
               (map (subst σ) As) (map (subst σ) ms′)
      go []ₗ []ₗ []ₐ = []ₐ
      go (m ∷ₗ ms′) (A ∷ₗ As′) (([A] , [m]) ∷ₐ ps) =
        (proj₁ ([A] ⊢Δ [σ]) , proj₁ ([m] ⊢Δ [σ])) ∷ₐ go ms′ As′ ps

  -- Methods at σ and σ′ together with their equality.
  methodsσ≡ : ∀ {Γ Δ σ σ′ ind P rG lG ms l}
    → ([Γ] : ⊩ᵛ Γ)
    → (⊢Δ : ⊢ Δ)
    → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
    → ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
    → ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
    → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                      → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
           ms (indRectBranchTyList ind P rG lG)
    → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                         → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A]))
           (indRectBranchTyList ind (subst (liftSubst σ) P) rG lG)
           (map (subst σ) ms) (map (subst σ′) ms)
  methodsσ≡ {Δ = Δ} {σ = σ} {σ′ = σ′} {ind = ind} {P = P} {rG = rG} {lG = lG} {ms = ms} {l = l}
            [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [ms] =
    PE.subst (λ As → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                                       → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                                       × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                                       × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A]))
                          As (map (subst σ) ms) (map (subst σ′) ms))
             (subst-indRectBranchTyList σ ind P rG lG)
             (go ms (indRectBranchTyList ind P rG lG) [ms])
    where
      go : ∀ ms′ As →
        All₂ (λ m A → ∃ λ ([A] : _ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / _)
                        → _ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / _ / [A]) ms′ As
        → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                            → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                            × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                            × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A]))
               (map (subst σ) As) (map (subst σ) ms′) (map (subst σ′) ms′)
      go []ₗ []ₗ []ₐ = []ₐ
      go (m ∷ₗ ms′) (A ∷ₗ As′) (([A] , [m]) ∷ₐ ps) =
        let [σA]  = proj₁ ([A] ⊢Δ [σ])
            [σ′A] = proj₁ ([A] ⊢Δ [σ′])
            [A≡]  = proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]
        in  ([σA] , proj₁ ([m] ⊢Δ [σ])
                  , convTerm₂ [σA] [σ′A] [A≡] (proj₁ ([m] ⊢Δ [σ′]))
                  , proj₂ ([m] ⊢Δ [σ]) [σ′] [σ≡σ′])
            ∷ₐ go ms′ As′ ps

  -- Judgemental equality of the substituted methods.
  escapeMethodsσ≡ : ∀ {Γ Δ σ σ′ ind P rG lG ms l}
    → ([Γ] : ⊩ᵛ Γ)
    → (⊢Δ : ⊢ Δ)
    → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
    → ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
    → ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
    → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                      → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
           ms (indRectBranchTyList ind P rG lG)
    → Δ ⊢All map (subst σ) ms ≡ map (subst σ′) ms
        ∷ indRectBranchTyList ind (subst (liftSubst σ) P) rG lG ^ [ rG , ι lG ]
  escapeMethodsσ≡ {Δ = Δ} {σ = σ} {σ′ = σ′} {ind = ind} {P = P} {rG = rG} {lG = lG} {ms = ms}
                  [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [ms] =
    PE.subst (λ As → Δ ⊢All map (subst σ) ms ≡ map (subst σ′) ms ∷ As ^ [ rG , ι lG ])
             (subst-indRectBranchTyList σ ind P rG lG)
             (go ms (indRectBranchTyList ind P rG lG) [ms])
    where
      go : ∀ ms′ As →
        All₂ (λ m A → ∃ λ ([A] : _ ⊩ᵛ⟨ _ ⟩ A ^ [ rG , ι lG ] / _)
                        → _ ⊩ᵛ⟨ _ ⟩ m ∷ A ^ [ rG , ι lG ] / _ / [A]) ms′ As
        → Δ ⊢All map (subst σ) ms′ ≡ map (subst σ′) ms′ ∷ map (subst σ) As ^ [ rG , ι lG ]
      go []ₗ []ₗ []ₐ = εⱼ
      go (m ∷ₗ ms′) (A ∷ₗ As′) (([A] , [m]) ∷ₐ ps) =
        consⱼ (≅ₜ-eq (escapeTermEq (proj₁ ([A] ⊢Δ [σ]))
                                   (proj₂ ([m] ⊢Δ [σ]) [σ′] [σ≡σ′])))
              (go ms′ As′ ps)

IndRectᵛ : ∀ {Γ ind P rG lG t ms l}
         → (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
         → ([Γ] : ⊩ᵛ Γ)
         → (ind∈ : ind ∈ₗ senv)
         → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
         → ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P ^ [ rG , ι lG ] / [Γ] ∙ [Ind])
         → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
         → ([Pt] : Γ ⊩ᵛ⟨ l ⟩ P [ t ] ^ [ rG , ι lG ] / [Γ])
         → Γ ⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ]
         → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                         → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                ms (indRectBranchTyList ind P rG lG)
         → Γ ⊩ᵛ⟨ l ⟩ IndRect (SU.SInd.name ind) lG P t ms ∷ P [ t ] ^ [ rG , ι lG ] / [Γ] / [Pt]
IndRectᵛ {Γ = Γ} {ind = ind} {P = P} {rG = rG} {lG = lG} {t = t} {ms = ms} {l = l}
         rGlG [Γ] ind∈ [Ind] [P] [t] [Pt] ⊢ms [ms] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σt]   = ⟦t⟧ ⊢Δ [σ]
      eqPrf  = PE.trans (singleSubstComp (subst σ t) σ P)
                 (PE.sym (PE.trans (substCompEq P) (substConcatSingleton′ P)))
      ⊢msσ   = escapeMethodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms]
      [msσ]  = methodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms]
      [res]  = irrelevanceTerm′ eqPrf PE.refl PE.refl (Pu ⊢Δ [σ] [σt]) (proj₁ ([Pt] ⊢Δ [σ]))
                 (IndRectTerm rGlG ⊢Δ ind∈ (P∙ ⊢Δ [σ]) (Pu ⊢Δ [σ]) (Pu≡ ⊢Δ [σ])
                              ⊢msσ [msσ] [σt])
  in  PE.subst (λ x → Δ ⊩⟨ l ⟩ x ∷ subst σ (P [ t ]) ^ [ rG , ι lG ] / proj₁ ([Pt] ⊢Δ [σ]))
               (PE.sym (subst-IndRect σ (SU.SInd.name ind) lG P t ms)) [res]
    , (λ {σ′} [σ′] [σ≡σ′] →
         let [σt]    = ⟦t⟧ ⊢Δ [σ]
             [σ′t]   = ⟦t⟧ ⊢Δ [σ′]
             [σt≡]   = irrelevanceEqTerm (proj₁ ([Ind] ⊢Δ [σ]))
                         (Indᵣ {l = l} (idRed:*: (univ (Indⱼ ⊢Δ))))
                         (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
             eqPrf   = PE.trans (singleSubstComp (subst σ t) σ P)
                         (PE.sym (PE.trans (substCompEq P) (substConcatSingleton′ P)))
             ⊢msσ    = escapeMethodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms]
             ⊢msσ′   = escapeMethodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ′] [ms]
             ⊢msσ≡   = escapeMethodsσ≡ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [ms]
             [msσ′]  = methodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ′] [ms]
             [msσ≡]  = methodsσ≡ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [ms]
             [res]   = irrelevanceEqTerm′ eqPrf PE.refl PE.refl
                         (Pu ⊢Δ [σ] [σt]) (proj₁ ([Pt] ⊢Δ [σ]))
                         (IndRect-congTerm rGlG ⊢Δ ind∈ (P∙ ⊢Δ [σ]) (P∙ ⊢Δ [σ′])
                            (P∙≡ ⊢Δ [σ] [σ′] [σ≡σ′])
                            (Pu ⊢Δ [σ]) (Pu≡ ⊢Δ [σ]) (Pu ⊢Δ [σ′]) (Pu≡ ⊢Δ [σ′])
                            (PP′u ⊢Δ [σ] [σ′] [σ≡σ′])
                            ⊢msσ ⊢msσ′ ⊢msσ≡ [msσ′] [msσ≡] [σt] [σ′t] [σt≡])
         in  PE.subst₂ (λ x y → Δ ⊩⟨ l ⟩ x ≡ y ∷ subst σ (P [ t ]) ^ [ rG , ι lG ]
                                  / proj₁ ([Pt] ⊢Δ [σ]))
                       (PE.sym (subst-IndRect σ (SU.SInd.name ind) lG P t ms))
                       (PE.sym (subst-IndRect σ′ (SU.SInd.name ind) lG P t ms)) [res])
  where
  -- The inductive type, the motive and its instances read off [Ind] / [P]
  -- at an arbitrary substitution.
  ⟦Ind⟧ : ∀ {Δ₁} (⊢Δ₁ : ⊢ Δ₁) → Δ₁ ⊩⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
  ⟦Ind⟧ ⊢Δ₁ = Indᵣ {l = l} (idRed:*: (univ (Indⱼ ⊢Δ₁)))

  ⟦t⟧ : ∀ {Δ₁ σ₁} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
      → Δ₁ ⊩Ind subst σ₁ t ∷Ind SU.SInd.name ind
  ⟦t⟧ ⊢Δ₁ [σ₁] = irrelevanceTerm (proj₁ ([Ind] ⊢Δ₁ [σ₁])) (⟦Ind⟧ ⊢Δ₁)
                   (proj₁ ([t] ⊢Δ₁ [σ₁]))

  ⟦u⟧ : ∀ {Δ₁ σ₁ u} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
      → Δ₁ ⊩Ind u ∷Ind SU.SInd.name ind
      → Δ₁ ⊩⟨ l ⟩ u ∷ subst σ₁ (Ind (SU.SInd.name ind)) ^ [ ! , ι ⁰ ]
          / proj₁ ([Ind] ⊢Δ₁ [σ₁])
  ⟦u⟧ ⊢Δ₁ [σ₁] [u] = irrelevanceTerm (⟦Ind⟧ ⊢Δ₁) (proj₁ ([Ind] ⊢Δ₁ [σ₁])) [u]

  ⟦u≡⟧ : ∀ {Δ₁ σ₁ u u′} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
       → Δ₁ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
       → Δ₁ ⊩⟨ l ⟩ u ≡ u′ ∷ subst σ₁ (Ind (SU.SInd.name ind)) ^ [ ! , ι ⁰ ]
           / proj₁ ([Ind] ⊢Δ₁ [σ₁])
  ⟦u≡⟧ ⊢Δ₁ [σ₁] [u≡u′] = irrelevanceEqTerm (⟦Ind⟧ ⊢Δ₁) (proj₁ ([Ind] ⊢Δ₁ [σ₁])) [u≡u′]

  P∙ : ∀ {Δ₁ σ₁} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
     → Δ₁ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ subst (liftSubst σ₁) P ^ [ rG , ι lG ]
  P∙ ⊢Δ₁ [σ₁] = proj₁ ([P] (⊢Δ₁ ∙ escape (proj₁ ([Ind] ⊢Δ₁ [σ₁])))
                           (liftSubstS {F = Ind (SU.SInd.name ind)} [Γ] ⊢Δ₁ [Ind] [σ₁]))

  P∙≡ : ∀ {Δ₁ σ₁ σ₂} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
          ([σ₂] : Δ₁ ⊩ˢ σ₂ ∷ Γ / [Γ] / ⊢Δ₁)
          ([σ₁≡σ₂] : Δ₁ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / [Γ] / ⊢Δ₁ / [σ₁])
        → Δ₁ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩
            subst (liftSubst σ₁) P ≡ subst (liftSubst σ₂) P ^ [ rG , ι lG ] / P∙ ⊢Δ₁ [σ₁]
  P∙≡ {σ₂ = σ₂} ⊢Δ₁ [σ₁] [σ₂] [σ₁≡σ₂] =
    proj₂ ([P] (⊢Δ₁ ∙ escape (proj₁ ([Ind] ⊢Δ₁ [σ₁])))
               (liftSubstS {F = Ind (SU.SInd.name ind)} [Γ] ⊢Δ₁ [Ind] [σ₁]))
          (S.irrelevanceSubst {σ = liftSubst σ₂} (_∙_ {A = Ind (SU.SInd.name ind)} [Γ] [Ind])
             (_∙_ {A = Ind (SU.SInd.name ind)} [Γ] [Ind])
             (⊢Δ₁ ∙ escape (proj₁ ([Ind] ⊢Δ₁ [σ₂])))
             (⊢Δ₁ ∙ escape (proj₁ ([Ind] ⊢Δ₁ [σ₁])))
             (liftSubstS {F = Ind (SU.SInd.name ind)} [Γ] ⊢Δ₁ [Ind] [σ₂]))
          (liftSubstSEq {F = Ind (SU.SInd.name ind)} [Γ] ⊢Δ₁ [Ind] [σ₁] [σ₁≡σ₂])

  Pu : ∀ {Δ₁ σ₁ u} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
     → Δ₁ ⊩Ind u ∷Ind SU.SInd.name ind
     → Δ₁ ⊩⟨ l ⟩ subst (liftSubst σ₁) P [ u ] ^ [ rG , ι lG ]
  Pu {σ₁ = σ₁} {u = u} ⊢Δ₁ [σ₁] [u] =
    irrelevance′ (PE.sym (singleSubstComp u σ₁ P))
      (proj₁ ([P] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u])))

  PP′u : ∀ {Δ₁ σ₁ σ₂} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
           ([σ₂] : Δ₁ ⊩ˢ σ₂ ∷ Γ / [Γ] / ⊢Δ₁)
           ([σ₁≡σ₂] : Δ₁ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / [Γ] / ⊢Δ₁ / [σ₁])
           {u u′} ([u] : Δ₁ ⊩Ind u ∷Ind SU.SInd.name ind)
           ([u′] : Δ₁ ⊩Ind u′ ∷Ind SU.SInd.name ind)
         → Δ₁ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
         → Δ₁ ⊩⟨ l ⟩ subst (liftSubst σ₁) P [ u ] ≡ subst (liftSubst σ₂) P [ u′ ]
             ^ [ rG , ι lG ] / Pu ⊢Δ₁ [σ₁] [u]
  PP′u {σ₁ = σ₁} {σ₂ = σ₂} ⊢Δ₁ [σ₁] [σ₂] [σ₁≡σ₂] {u} {u′} [u] [u′] [u≡u′] =
    irrelevanceEq″ (PE.sym (singleSubstComp u σ₁ P)) (PE.sym (singleSubstComp u′ σ₂ P))
      PE.refl PE.refl
      (proj₁ ([P] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u]))) (Pu ⊢Δ₁ [σ₁] [u])
      (proj₂ ([P] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u]))
             ([σ₂] , ⟦u⟧ ⊢Δ₁ [σ₂] [u′])
             ([σ₁≡σ₂] , ⟦u≡⟧ ⊢Δ₁ [σ₁] [u≡u′]))

  Pu≡ : ∀ {Δ₁ σ₁} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
          {u u′} ([u] : Δ₁ ⊩Ind u ∷Ind SU.SInd.name ind)
          ([u′] : Δ₁ ⊩Ind u′ ∷Ind SU.SInd.name ind)
        → Δ₁ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
        → Δ₁ ⊩⟨ l ⟩ subst (liftSubst σ₁) P [ u ] ≡ subst (liftSubst σ₁) P [ u′ ]
            ^ [ rG , ι lG ] / Pu ⊢Δ₁ [σ₁] [u]
  Pu≡ ⊢Δ₁ [σ₁] = PP′u ⊢Δ₁ [σ₁] [σ₁] (reflSubst [Γ] ⊢Δ₁ [σ₁])

-- variable-arity apps make a direct clone impractical.
postulate
  IndRect-ctr-rhsᵛ : ∀ {Γ ind j P rG lG args ms m Ts l}
                   → (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
                   → ([Γ] : ⊩ᵛ Γ)
                   → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
                   → ([d] : Γ ⊩ᵛ⟨ l ⟩ ctr (SU.SInd.name ind) j args ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
                   → ([Pd] : Γ ⊩ᵛ⟨ l ⟩ P [ ctr (SU.SInd.name ind) j args ] ^ [ rG , ι lG ] / [Γ])
                   → SU.ctrArgsTypeList ind j PE.≡ just Ts
                   → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
                   → Γ ⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ]
                   → nth ms j PE.≡ just m
                   → Γ ⊩ᵛ⟨ l ⟩ apps lG m
                                        (args ++ map (λ a → IndRect (SU.SInd.name ind) lG P a ms) args)
                              ∷ P [ ctr (SU.SInd.name ind) j args ] ^ [ rG , ι lG ] / [Γ] / [Pd]

------------------------------------------------------------------------
-- Validity of IndRect congruence.
-- ⊢ms' is under P (as in Typed IndRect-cong / ⊢All equality), not P'.
postulate
  IndRect-congᵛ : ∀ {ind P P' rG lG t t' ms ms' Γ l}
              (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
              ([Γ] : ⊩ᵛ Γ)
              ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
              ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P ^ [ rG , ι lG ] / [Γ] ∙ [Ind])
              ([P'] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P' ^ [ rG , ι lG ] / [Γ] ∙ [Ind])
              ([P≡P'] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P ≡ P' ^ [ rG , ι lG ] / [Γ] ∙ [Ind] / [P])
              ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              ([t'] : Γ ⊩ᵛ⟨ l ⟩ t' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              ([t≡t'] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              ([Pt] : Γ ⊩ᵛ⟨ l ⟩ P [ t ] ^ [ rG , ι lG ] / [Γ])
              (⊢ms : Γ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ])
              (⊢ms' : Γ ⊢All ms' ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ])
              (⊢ms≡ : Γ ⊢All ms ≡ ms' ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ])
              (rG≡! : rG PE.≡ !)
            → Γ ⊩ᵛ⟨ l ⟩ IndRect (SU.SInd.name ind) lG P t ms ≡ IndRect (SU.SInd.name ind) lG P' t' ms' ∷ P [ t ] ^ [ rG , ι lG ] / [Γ] / [Pt]

------------------------------------------------------------------------
