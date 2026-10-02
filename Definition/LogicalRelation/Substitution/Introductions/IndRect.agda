{-# OPTIONS --safe #-}

import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.IndRect (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}

open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Untyped.IndRect senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.RedSteps senv equivs
open import Definition.LogicalRelation senv swf equivs
open import Definition.LogicalRelation.ShapeView senv swf equivs
open import Definition.LogicalRelation.Irrelevance senv swf equivs
open import Definition.LogicalRelation.Properties senv swf equivs
open import Definition.LogicalRelation.Application senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Application senv swf equivs
open import Definition.LogicalRelation.Substitution senv swf equivs
open import Definition.LogicalRelation.Substitution.Properties senv swf equivs
open import Definition.LogicalRelation.Substitution.Escape senv swf equivs
open import Definition.LogicalRelation.Substitution.Reflexivity senv swf equivs
import Definition.LogicalRelation.Substitution.Irrelevance senv swf equivs as S
open import Definition.LogicalRelation.Substitution.Introductions.Ind senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst senv swf equivs
open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Nullary using (Dec; yes; no)
open import Tools.List using (List; All; All₂; All₃; range-suc; ∷-inj₁; ∷-inj₂; []ₐ; _∷ₐ_; map; _++_; lookupDefault; nth; length; length-map; All₂-length; lookupAll₂; all∈; length-range;
                              range; zip; foldr; _∈ₗ_; hereₗ; thereₗ;
                              nth-length; nth-map; nth-zip-range; nth-lookupDefault; nthAll₂; nthAll₃)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Tools.Maybe using (just)
open import Tools.Inequality using (Bool; true; false; eqb; eqb-refl; eqb-no; if_then_else_; filter)
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
-- Helpers for IndRectTerm and IndRectᵛ below

private
  reflAllEq′ : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → Γ ⊢All ts ≡ ts ∷ As ^ r
  reflAllEq′ εⱼ = εⱼ
  reflAllEq′ (consⱼ {r = [ ! , l ]} ⊢t ⊢ts) = consⱼ (refl ⊢t) (reflAllEq′ ⊢ts)
  reflAllEq′ (consⱼ {r = [ % , l ]} ⊢t ⊢ts) = consⱼ (proof-irrelevance ⊢t ⊢t) (reflAllEq′ ⊢ts)

  -- Reducible methods are reflexively ≅.
  escapeMethods≅ : ∀ {Δ As ms rG lG l}
    → All₂ (λ A m → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                      → Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A]) As ms
    → All₃ (λ m m′ A → Δ ⊢ m ≅ m′ ∷ A ^ [ rG , ι lG ]) ms ms As
  escapeMethods≅ []ₐ = []ₐ
  escapeMethods≅ (([A] , [m]) ∷ₐ ps) = escapeTermEq [A] (reflEqTerm [A] [m]) ∷ₐ escapeMethods≅ ps

  -- The left methods of a reducible equality of methods are reflexively ≅.
  escapeMethodsˡ≅ : ∀ {Δ As ms ms′ rG lG l}
    → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                         → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A])) As ms ms′
    → All₃ (λ m m′ A → Δ ⊢ m ≅ m′ ∷ A ^ [ rG , ι lG ]) ms ms As
  escapeMethodsˡ≅ []ₐ = []ₐ
  escapeMethodsˡ≅ (([A] , [m] , _ , _) ∷ₐ ps) = escapeTermEq [A] (reflEqTerm [A] [m]) ∷ₐ escapeMethodsˡ≅ ps

  -- Escape of a reducible equality of methods.
  escapeMethodsEq≅ : ∀ {Δ As ms ms′ rG lG l}
    → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                         → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A])) As ms ms′
    → All₃ (λ m m′ A → Δ ⊢ m ≅ m′ ∷ A ^ [ rG , ι lG ]) ms ms′ As
  escapeMethodsEq≅ []ₐ = []ₐ
  escapeMethodsEq≅ (([A] , _ , _ , [m≡]) ∷ₐ ps) = escapeTermEq [A] [m≡] ∷ₐ escapeMethodsEq≅ ps

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
  -- wk1^ ℓ (P [ bℓ ]), bℓ being the instance of its recursive argument.
  subst-tel-inst : ∀ σ n P d (rs : List Nat) →
    (∀ x → σ (n + x) PE.≡ var x) →
    subst-tel σ d (ihGo n P d rs) PE.≡
    mapwk1^ d (wkTele (map (λ b → P [ b ]) (map (λ r → subst σ (var ((n - 1) - r))) rs)))
  subst-tel-inst σ n P d []ₗ hσ = PE.sym (mapwk1^-[] d)
  subst-tel-inst σ n P d (r ∷ₗ rs) hσ =
    PE.trans
      (PE.cong₂ _∷ₗ_ headEq (subst-tel-inst σ n P (1+ d) rs hσ))
      (PE.sym (mapwk1^-∷ d (P [ b ]) (map wk1 (wkTele (map (λ b → P [ b ]) bs)))))
    where
    b  = subst σ (var ((n - 1) - r))
    bs = map (λ r → subst σ (var ((n - 1) - r))) rs

    headEq : subst (repeat liftSubst σ d) (ihFun n P r d) PE.≡ wk1^ d (P [ b ])
    headEq =
      subst-Pat σ n P d (var (((n - 1) - r) + d)) b hσ
        (PE.trans (PE.cong (repeat liftSubst σ d) (plus-comm ((n - 1) - r) d))
                  (substVar-lifts-≥ d σ ((n - 1) - r)))

  -- Instantiating the conclusion, under the k hypotheses.
  subst-concl : ∀ σ i j P n k (as : List Term) → n PE.≡ length as →
    (∀ x → σ (n + x) PE.≡ var x) →
    (∀ q → q << n → subst σ (var ((n - 1) - q)) PE.≡ lookupDefault (var 0) as q) →
    subst (repeat liftSubst σ k) (concl i j P n k) PE.≡ wk1^ k (P [ ctr i j as ])
  subst-concl σ i j P n k as n≡ hσ hv =
    PE.trans
      (PE.cong (λ m → subst (repeat liftSubst σ k) (P [ ctr i j (ctrVars n k) ]↑^ m))
               (plus-comm k n))
      (subst-Pat σ n P k (ctr i j (ctrVars n k)) (ctr i j as) hσ
        (PE.trans (subst-ctr (repeat liftSubst σ k) i j (ctrVars n k))
          (PE.trans
            (PE.cong (ctr i j)
              (PE.trans (map-map (subst (repeat liftSubst σ k))
                                 (λ v → var (((k + n) - 1) - v)) (range n))
                varsEq))
            (PE.sym (wk1^-ctr k i j as)))))
    where
    varsEq : map (λ v → subst (repeat liftSubst σ k) (var (((k + n) - 1) - v))) (range n)
             PE.≡ map (wk1^ k) as
    varsEq =
      PE.trans
        (PE.cong (λ m → map (λ v → subst (repeat liftSubst σ k) (var (((k + n) - 1) - v)))
                            (range m))
          (PE.trans n≡ (PE.sym (length-map (wk1^ k) as))))
        (map-range-≡ (var 0)
          (λ v → subst (repeat liftSubst σ k) (var (((k + n) - 1) - v)))
          (map (wk1^ k) as)
          (λ q hq →
            let hq′ : q << n
                hq′ = PE.subst (λ m → q << m)
                        (PE.trans (length-map (wk1^ k) as) (PE.sym n≡)) hq
            in PE.trans
                 (PE.cong (repeat liftSubst σ k) (varIdx k n q hq′))
                 (PE.trans (substVar-lifts-≥ k σ ((n - 1) - q))
                   (PE.trans (PE.cong (wk1^ k) (hv q hq′))
                     (PE.sym (lookupDefault-map (wk1^ k) (var 0) (var 0) as q
                               (PE.subst (λ m → q << m) n≡ hq′)))))))

  -- The method body, with all n argument binders instantiated by as: the
  -- hypotheses become P [ b ] for the recursive arguments b of as.
  instBody : ∀ i j Ts P lG (as : List Term) → ctrArity Ts PE.≡ length as →
    subst (argSubst as)
      (foldr (Πih ! lG) (concl i j P (ctrArity Ts) (length (ctrRecIndices i Ts)))
                        (ihGo (ctrArity Ts) P 0 (ctrRecIndices i Ts)))
    PE.≡ arrows lG (map (λ a → P [ a ]) (ctrRecArgs i Ts as)) (P [ ctr i j as ])
  instBody i j Ts P lG as n≡ =
    PE.trans
      (PE.trans
        (subst-foldr-Π (argSubst as) ! lG lG ! (concl i j P n k) (ihGo n P 0 rs))
        (PE.cong₂ (foldr (Πih ! lG))
          (PE.trans
            (PE.cong (λ m → subst (repeat liftSubst (argSubst as) m) (concl i j P n k))
                     (length-ihGo n P 0 rs))
            (subst-concl (argSubst as) i j P n k as n≡ hσ hv))
          (subst-tel-inst (argSubst as) n P 0 rs hσ)))
      (PE.trans
        (PE.cong₂ (λ m L → foldr (Πih ! lG) (wk1^ m (P [ ctr i j as ]))
                                 (wkTele (map (λ a → P [ a ]) L)))
          (PE.sym (PE.trans (length-map (λ a → P [ a ]) bs)
                    (PE.trans (PE.cong length (PE.sym recsEq)) (length-map f rs))))
          recsEq)
        (arrows-foldr lG (map (λ a → P [ a ]) bs) (P [ ctr i j as ])))
    where
    n  = ctrArity Ts
    rs = ctrRecIndices i Ts
    k  = length rs
    bs = ctrRecArgs i Ts as
    f  = λ r → subst (argSubst as) (var ((n - 1) - r))

    hσ : ∀ x → argSubst as (n + x) PE.≡ var x
    hσ x = PE.trans (PE.cong (λ m → argSubst as (m + x)) n≡) (argSubst-shift as x)

    hv : ∀ q → q << n → subst (argSubst as) (var ((n - 1) - q))
                        PE.≡ lookupDefault (var 0) as q
    hv q hq =
      PE.trans (PE.cong (λ m → subst (argSubst as) (var ((m - 1) - q))) n≡)
               (argSubst-var as q (PE.subst (λ m → q << m) n≡ hq))

    -- The argument binders are sent to as ...
    varsEq : map f (range n) PE.≡ as
    varsEq =
      PE.trans (PE.cong (λ m → map f (range m)) n≡)
        (map-range-≡ (var 0) f as
          (λ q hq → hv q (PE.subst (λ m → q << m) (PE.sym n≡) hq)))

    -- ... hence the recursive ones to the recursive arguments.
    recsEq : map f rs PE.≡ bs
    recsEq =
      PE.trans (map-ctrRecIndices f i (range n) Ts)
               (PE.cong (λ xs → ctrRecArgs i Ts xs) varsEq)

-- Reducible constructor arguments: each one lives at its own (closed) type.
RedArg : Con Term → TypeLevel → Term → Term → Set
RedArg Δ l a A = ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ]) → Δ ⊩⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [A]

RedArgEq : Con Term → TypeLevel → Term → Term → Term → Set
RedArgEq Δ l a a′ A = ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ])
                        → (Δ ⊩⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [A])
                        × (Δ ⊩⟨ l ⟩ a′ ∷ A ^ [ ! , ι ⁰ ] / [A])
                        × (Δ ⊩⟨ l ⟩ a ≡ a′ ∷ A ^ [ ! , ι ⁰ ] / [A])

private
  -- The arguments of a reducible constructor, at their inductive types.
  argsRed : ∀ {Δ l Ts as} → ⊢ Δ → All (SU.indsInSEnv senv) Ts
          → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ∷Ind k) as (map emb-stype Ts)
          → All₂ (RedArg Δ l) as (map emb-stype Ts)
  argsRed {Ts = []ₗ} ⊢Δ []ₐ []ₐ = []ₐ
  argsRed {Ts = SU.Ind _ ∷ₗ Ts} ⊢Δ (k∈ ∷ₐ ks) ((k , PE.refl , [a]) ∷ₐ ps) =
    (Indᵣ (idRed:*: (univ (Indⱼ′ ⊢Δ k∈))) , [a]) ∷ₐ argsRed ⊢Δ ks ps
  argsRed {Ts = SU.Arrow _ _ ∷ₗ Ts} ⊢Δ _ ((k , () , _) ∷ₐ ps)

  argsRedEq : ∀ {Δ l Ts as as′} → ⊢ Δ → All (SU.indsInSEnv senv) Ts
            → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ∷Ind k) as (map emb-stype Ts)
            → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ∷Ind k) as′ (map emb-stype Ts)
            → All₃ (λ a a′ A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ≡ a′ ∷Ind k) as as′ (map emb-stype Ts)
            → All₃ (RedArgEq Δ l) as as′ (map emb-stype Ts)
  argsRedEq {Ts = []ₗ} ⊢Δ []ₐ []ₐ []ₐ []ₐ = []ₐ
  argsRedEq {Ts = SU.Ind _ ∷ₗ Ts} ⊢Δ (k∈ ∷ₐ ks) ((k , PE.refl , [a]) ∷ₐ ps)
            ((k′ , PE.refl , [a′]) ∷ₐ ps′) ((k″ , PE.refl , [a≡a′]) ∷ₐ pps) =
    (Indᵣ (idRed:*: (univ (Indⱼ′ ⊢Δ k∈))) , [a] , [a′] , [a≡a′])
    ∷ₐ argsRedEq ⊢Δ ks ps ps′ pps
  argsRedEq {Ts = SU.Arrow _ _ ∷ₗ Ts} ⊢Δ _ ((k , () , _) ∷ₐ ps) _ _

------------------------------------------------------------------------
-- Reducible application of a method to the constructor arguments and to
-- the induction hypotheses.

private
  -- Argument phase: the domains are closed types, so the telescope is
  -- peeled one binder at a time by appTerm / substSΠ₁.
  appsArg : ∀ {Δ lG l Body t} {Ts : List SU.Type} {as : List Term}
          → All₂ (RedArg Δ l) as (map emb-stype Ts)
          → ([T] : Δ ⊩⟨ l ⟩ foldr (Πarg ! lG) Body (map emb-stype Ts) ^ [ ! , ι lG ])
          → Δ ⊩⟨ l ⟩ t ∷ foldr (Πarg ! lG) Body (map emb-stype Ts) ^ [ ! , ι lG ] / [T]
          → ∃ λ ([R] : Δ ⊩⟨ l ⟩ subst (argSubst as) Body ^ [ ! , ι lG ])
              → Δ ⊩⟨ l ⟩ apps lG t as ∷ subst (argSubst as) Body ^ [ ! , ι lG ] / [R]
  appsArg {Body = Body} {Ts = []ₗ} []ₐ [T] [t] =
    let [R] = irrelevance′ (PE.sym (subst-id Body)) [T]
    in  [R] , irrelevanceTerm′ (PE.sym (subst-id Body)) PE.refl PE.refl [T] [R] [t]
  appsArg {lG = lG} {Body = Body} {Ts = T ∷ₗ Ts} {as = a ∷ₗ as} (([A] , [a]) ∷ₐ [as]) [T] [t] =
    let n     = length as
        Body′ = subst (repeat liftSubst (sgSubst a) n) Body
        eqB   = PE.trans (subst-foldr-Π-closed (sgSubst a) ! ⁰ lG ! Body
                            (map emb-stype Ts) (λ σ' → map-subst-emb-stype σ' Ts))
                  (PE.cong (λ m → foldr (Πarg ! lG)
                                    (subst (repeat liftSubst (sgSubst a) m) Body)
                                    (map emb-stype Ts))
                           (PE.sym (All₂-length [as])))
        [Ta]  = substSΠ₁ [T] [A] [a]
        [Ta]′ = irrelevance′ eqB [Ta]
        [ta]  = irrelevanceTerm′ eqB PE.refl PE.refl [Ta] [Ta]′
                  (appTerm PE.refl [A] [Ta] [T] [t] [a])
        [R]′  = proj₁ (appsArg {Body = Body′} {Ts = Ts} [as] [Ta]′ [ta])
        [r]′  = proj₂ (appsArg {Body = Body′} {Ts = Ts} [as] [Ta]′ [ta])
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
    → All₂ (RedArg Δ l) args (map emb-stype Ts)
    → ([T] : Δ ⊩⟨ l ⟩ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ])
    → Δ ⊩⟨ l ⟩ m ∷ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ] / [T]
    → All₂ (λ D u → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                      → Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
           (map (λ a → P [ a ]) (ctrRecArgs i Ts args)) ihs
    → ∃ λ ([E] : Δ ⊩⟨ l ⟩ (P [ ctr i j args ]) ^ [ ! , ι lG ])
        → Δ ⊩⟨ l ⟩ apps lG m (args ++ ihs) ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E]
  appsMethod {i = i} {j = j} {Ts = Ts} {P = P} {lG = lG} {m = m} {args = args} {ihs = ihs}
             [args] [T] [m] [ihs] =
    let n     = ctrArity Ts
        n≡    = PE.sym (PE.trans (All₂-length [args]) (length-map emb-stype Ts))
        Body₀ = foldr (Πih ! lG) (concl i j P n (length (ctrRecIndices i Ts)))
                                 (ihGo n P 0 (ctrRecIndices i Ts))
        eqT   = branchTy-nf i j Ts P ! lG
        [T]′  = irrelevance′ eqT [T]
        [m]′  = irrelevanceTerm′ eqT PE.refl PE.refl [T] [T]′ [m]
        [R]   = proj₁ (appsArg {Body = Body₀} {Ts = Ts} [args] [T]′ [m]′)
        [r]   = proj₂ (appsArg {Body = Body₀} {Ts = Ts} [args] [T]′ [m]′)
        eqR   = instBody i j Ts P lG args n≡
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
  argFst : ∀ {Δ l} {as as′ As : List Term}
         → All₃ (RedArgEq Δ l) as as′ As → All₂ (RedArg Δ l) as As
  argFst []ₐ = []ₐ
  argFst (([A] , [a] , _ , _) ∷ₐ ps) = ([A] , [a]) ∷ₐ argFst ps

  argSnd : ∀ {Δ l} {as as′ As : List Term}
         → All₃ (RedArgEq Δ l) as as′ As → All₂ (RedArg Δ l) as′ As
  argSnd []ₐ = []ₐ
  argSnd (([A] , _ , [a′] , _) ∷ₐ ps) = ([A] , [a′]) ∷ₐ argSnd ps

  appsArg-cong : ∀ {Δ lG l Body t t′} {Ts : List SU.Type} {as as′ : List Term}
             → All₃ (RedArgEq Δ l) as as′ (map emb-stype Ts)
             → ([T] : Δ ⊩⟨ l ⟩ foldr (Πarg ! lG) Body (map emb-stype Ts) ^ [ ! , ι lG ])
             → Δ ⊩⟨ l ⟩ t ≡ t′ ∷ foldr (Πarg ! lG) Body (map emb-stype Ts)
                           ^ [ ! , ι lG ] / [T]
             → ([R] : Δ ⊩⟨ l ⟩ subst (argSubst as) Body ^ [ ! , ι lG ])
             → Δ ⊩⟨ l ⟩ apps lG t as ≡ apps lG t′ as′ ∷ subst (argSubst as) Body
                           ^ [ ! , ι lG ] / [R]
  appsArg-cong {Body = Body} {Ts = []ₗ} []ₐ [T] [t≡t′] [R] =
    irrelevanceEqTerm′ (PE.sym (subst-id Body)) PE.refl PE.refl [T] [R] [t≡t′]
  appsArg-cong {lG = lG} {Body = Body} {Ts = T ∷ₗ Ts} {as = a ∷ₗ as}
               (([A] , [a] , [a′] , [a≡a′]) ∷ₐ [aa]) [T] [t≡t′] [R] =
    let n     = length as
        Body′ = subst (repeat liftSubst (sgSubst a) n) Body
        eqB   = PE.trans (subst-foldr-Π-closed (sgSubst a) ! ⁰ lG ! Body
                            (map emb-stype Ts) (λ σ' → map-subst-emb-stype σ' Ts))
                  (PE.cong (λ m → foldr (Πarg ! lG)
                                    (subst (repeat liftSubst (sgSubst a) m) Body)
                                    (map emb-stype Ts))
                           (PE.sym (All₂-length (argFst [aa]))))
        [Ta]  = substSΠ₁ [T] [A] [a]
        [Ta]′ = irrelevance′ eqB [Ta]
        [ta≡] = irrelevanceEqTerm′ eqB PE.refl PE.refl [Ta] [Ta]′
                  (app-congTerm [A] [Ta] [T] [t≡t′] [a] [a′] [a≡a′])
        eqR   = substCompEq {σ = argSubst as} {σ′ = repeat liftSubst (sgSubst a) n} Body
        [R]′  = irrelevance′ (PE.sym eqR) [R]
        rec   = appsArg-cong {Body = Body′} {Ts = Ts} [aa] [Ta]′ [ta≡] [R]′
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

  -- The β-reduct congruence: the j-th methods applied to the constructor
  -- arguments and then to the induction hypotheses.
  appsMethod-cong : ∀ {Δ i j Ts P lG l m m′ args args′ ihs ihs′}
    → All₃ (RedArgEq Δ l) args args′ (map emb-stype Ts)
    → ([T] : Δ ⊩⟨ l ⟩ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ])
    → Δ ⊩⟨ l ⟩ m ∷ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ] / [T]
    → Δ ⊩⟨ l ⟩ m ≡ m′ ∷ indRectBranchTy i j Ts P ! lG ^ [ ! , ι lG ] / [T]
    → All₃ (λ D u u′ → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                         → (Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u′ ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u ≡ u′ ∷ D ^ [ ! , ι lG ] / [D]))
           (map (λ a → P [ a ]) (ctrRecArgs i Ts args)) ihs ihs′
    → ([E] : Δ ⊩⟨ l ⟩ (P [ ctr i j args ]) ^ [ ! , ι lG ])
    → Δ ⊩⟨ l ⟩ apps lG m (args ++ ihs) ≡ apps lG m′ (args′ ++ ihs′)
                  ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E]
  appsMethod-cong {i = i} {j = j} {Ts = Ts} {P = P} {lG = lG} {m = m} {m′ = m′}
                  {args = args} {args′ = args′} {ihs = ihs} {ihs′ = ihs′}
                  [aa] [T] [m] [m≡m′] [ihs] [E] =
    let n      = ctrArity Ts
        n≡     = PE.sym (PE.trans (All₂-length (argFst [aa])) (length-map emb-stype Ts))
        Body₀  = foldr (Πih ! lG) (concl i j P n (length (ctrRecIndices i Ts)))
                                  (ihGo n P 0 (ctrRecIndices i Ts))
        eqT    = branchTy-nf i j Ts P ! lG
        [T]′   = irrelevance′ eqT [T]
        [m]′   = irrelevanceTerm′ eqT PE.refl PE.refl [T] [T]′ [m]
        [m≡]′  = irrelevanceEqTerm′ eqT PE.refl PE.refl [T] [T]′ [m≡m′]
        [R]    = proj₁ (appsArg {Body = Body₀} {Ts = Ts} (argFst [aa]) [T]′ [m]′)
        eqR    = instBody i j Ts P lG args n≡
        [R]′   = irrelevance′ eqR [R]
        [ar≡]  = appsArg-cong {Body = Body₀} {Ts = Ts} [aa] [T]′ [m≡]′ [R]
        [ar≡]′ = irrelevanceEqTerm′ eqR PE.refl PE.refl [R] [R]′ [ar≡]
        [ih≡]  = appsIH-cong [ihs] [R]′ [ar≡]′ [E]
    in  PE.subst (λ x → _ ⊩⟨ _ ⟩ x ≡ apps lG m′ (args′ ++ ihs′)
                          ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E])
          (PE.sym (apps-++ lG m args ihs))
          (PE.subst (λ y → _ ⊩⟨ _ ⟩ apps lG (apps lG m args) ihs ≡ y
                             ∷ (P [ ctr i j args ]) ^ [ ! , ι lG ] / [E])
             (PE.sym (apps-++ lG m′ args′ ihs′)) [ih≡])

-- Reducibility of IndRect, by induction on the reducibility of the eliminated
-- term. The motive P lives in Δ ∙ Ind i; [Pu] and [Pu≡] give its reducible
-- instances P [ u ], so the definitions below stay in the ambient Δ.

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
    let [Ind] = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ ind∈)))
    in  logRelIrr ([Pu] [t])
                  (IndRectⱼ rGlG ind∈ (escape [P∙]) (escapeTerm [Ind] [t]) ⊢ms)
  IndRectTerm {ind = ind} {P = P} {rG = !} {lG = lG} {ms = ms} {l = l}
              rGlG ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms]
              (Indₜ k d k≡k (ne (neNfₜ neK ⊢k k~k))) =
    let [Ind]   = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ ind∈)))
        [t]     = Indₜ k d k≡k (ne (neNfₜ neK ⊢k k~k))
        ⊢P      = escape [P∙]
        ⊢P≅P    = escapeEq [P∙] (reflEq [P∙])
        [k]     = neuTerm [Ind] neK ⊢k k~k
        [t≡k]   = proj₂ (redSubst*Term (redₜ d) [Ind] [k])
        [Pt]    = [Pu] [t]
        [Pk]    = [Pu] [k]
        [Pt≡Pk] = [Pu≡] [t] [k] [t≡k]
        IndRectK = neuTerm [Pk] (IndRectₙ neK) (IndRectⱼ rGlG ind∈ ⊢P ⊢k ⊢ms)
                           (~-IndRect ind∈ ⊢P≅P k~k (escapeMethods≅ [ms]))
        reduction = IndRect-subst* ind∈ ⊢P (redₜ d) ⊢ms [Ind] [k]
                      (λ [u] [u′] [u≡u′] →
                         ≅-eq (escapeEq ([Pu] [u]) ([Pu≡] [u] [u′] [u≡u′])))
    in  proj₁ (redSubst*Term reduction [Pt]
                 (convTerm₂ [Pt] [Pk] [Pt≡Pk] IndRectK))
  IndRectTerm {ind = ind} {P = P} {rG = !} {lG = lG} {ms = ms} {l = l}
              rGlG ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms]
              (Indₜ .(ctr (SU.SInd.name ind) j args) d k≡k
                    (ctrᵣ {ind′} {j} {args} {Ts} ind∈′ name≡ eq ps))
    with SU.name-inj senv (proj₁ swf) ind∈′ ind∈ name≡
  ... | PE.refl =
    let i       = SU.SInd.name ind
        [Ind]   = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ ind∈)))
        [t]     = Indₜ (ctr i j args) d k≡k (ctrᵣ ind∈′ name≡ eq ps)
        ⊢P      = escape [P∙]
        ⊢ctr    = _⊢_:⇒*:_∷_^_.⊢u d
        [args]  = argsRed ⊢Δ (ctrArgInds ind∈ eq) ps
        ⊢args   = escapeArgs [args]
        [k]     = Indₜ (ctr i j args) (idRedTerm:*: ⊢ctr) k≡k (ctrᵣ ind∈′ name≡ eq ps)
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
        [E]     = proj₁ (appsMethod {j = j} {P = P} [args] [Tⱼ] [mⱼ] [ihs])
        [e]     = proj₂ (appsMethod {j = j} {P = P} [args] [Tⱼ] [mⱼ] [ihs])
        [e]′    = irrelevanceTerm [E] [Pk] [e]
        reduction = IndRect-subst* ind∈ ⊢P (redₜ d) ⊢ms [Ind] [k]
                      (λ [u] [u′] [u≡u′] →
                         ≅-eq (escapeEq ([Pu] [u]) ([Pu≡] [u] [u′] [u≡u′])))
                    ⇨∷* (conv* (IndRect-ctr ind∈ eq ⊢P ⊢args ⊢ms nthms
                                ⇨ id (escapeTerm [Pk] [e]′))
                               (sym (≅-eq (escapeEq [Pt] [Pt≡Pk]))))
    in  proj₁ (redSubst*Term reduction [Pt]
                 (convTerm₂ [Pt] [Pk] [Pt≡Pk] [e]′))

  -- The induction hypotheses: IndRect applied to each recursive argument.
  IndRectTerms : ∀ {Δ ind P lG ms l} {args : List Term} {Ts : List SU.Type}
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
    → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ∷Ind k) args (map emb-stype Ts)
    → All₂ (λ D u → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                      → Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
           (map (λ a → P [ a ]) (ctrRecArgs (SU.SInd.name ind) Ts args))
           (map (λ a → IndRect (SU.SInd.name ind) lG P a ms) (ctrRecArgs (SU.SInd.name ind) Ts args))
  IndRectTerms {Ts = []ₗ} ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] []ₐ = []ₐ
  IndRectTerms {ind = ind} {Ts = T ∷ₗ Ts} ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms]
               ((k , A≡ , [a]) ∷ₐ rest)
    with SU.ctrArgIsRecursive (SU.SInd.name ind) T in e
  ... | false = IndRectTerms ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] rest
  ... | true with rec-Ind (SU.SInd.name ind) T e
  ...   | PE.refl with A≡
  ...     | PE.refl =
    ([Pu] [a] , IndRectTerm (λ ()) ⊢Δ ind∈ [P∙] [Pu] [Pu≡] ⊢ms [ms] [a])
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
    let [Ind]      = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ ind∈)))
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
        [Ind]       = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ ind∈)))
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
                              (~-IndRect ind∈ ⊢P≅P k~k (escapeMethodsˡ≅ [ms≡]))
        IndRectK′   = neuTerm [P′k′] (IndRectₙ neK′) (IndRectⱼ rGlG ind∈ ⊢P′ ⊢k′ ⊢ms′)
                              (~-IndRect ind∈ ⊢P′≅P′ k′~k′ (escapeMethods≅ [ms′]))
        IndRectK≡K′ = convEqTerm₂ [Pt] [Pk] [Pt≡Pk]
                        (neuEqTerm [Pk] (IndRectₙ neK) (IndRectₙ neK′)
                          (IndRectⱼ rGlG ind∈ ⊢P ⊢k ⊢ms)
                          (conv (IndRectⱼ rGlG ind∈ ⊢P′ ⊢k′ ⊢ms′)
                                (sym (≅-eq (escapeEq [Pk] [Pk≡P′k′]))))
                          (~-IndRect ind∈ ⊢P≅P′
                            (PE.subst₂ (λ x y → _ ⊢ x ~ y ∷ _ ^ [ ! , ι ⁰ ])
                                       k₁≡k k₁′≡k′ k₁~k₁′)
                            (escapeMethodsEq≅ [ms≡])))
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
  IndRect-congTerm {ind = ind} {P = P} {P′ = P′} {rG = !} {lG = lG} {ms = ms} {ms′ = ms′} {l = l}
                   rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   (Indₜ .(ctr (SU.SInd.name ind) j args) d k≡k
                         (ctrᵣ {ind₁} {j} {args} {Ts} ind∈₁ name≡₁ eq ps))
                   (Indₜ .(ctr (SU.SInd.name ind) j′ args′) d′ k′≡k′
                         (ctrᵣ {ind₂} {j′} {args′} {Ts′} ind∈₂ name≡₂ eq′ ps′))
                   (Indₜ₌ .(ctr (SU.SInd.name ind) j₂ a₂) .(ctr (SU.SInd.name ind) j₂ a₂′)
                          d₁ d₁′ k₁≡k₁′ (ctrᵣ {ind₃} {j₂} {a₂} {a₂′} {Ts₃} ind∈₃ name≡₃ eq₃ aa))
    with ctr-PE-injectivity (whrDet*Term (redₜ d₁ , ctrₙ) (redₜ d , ctrₙ))
  ... | _ , PE.refl , PE.refl
    with ctr-PE-injectivity (whrDet*Term (redₜ d₁′ , ctrₙ) (redₜ d′ , ctrₙ))
  ... | _ , PE.refl , PE.refl
    with SU.name-inj senv (proj₁ swf) ind∈₁ ind∈ name≡₁
       | SU.name-inj senv (proj₁ swf) ind∈₂ ind∈ name≡₂
       | SU.name-inj senv (proj₁ swf) ind∈₃ ind∈ name≡₃
  ... | PE.refl | PE.refl | PE.refl
    with PE.trans (PE.sym eq) eq′ | PE.trans (PE.sym eq) eq₃
  ... | PE.refl | PE.refl =
    let i           = SU.SInd.name ind
        [Ind]       = Indᵣ {l = l} {i = SU.SInd.name ind} (idRed:*: (univ (Indⱼ ⊢Δ ind∈)))
        [ms]        = ihFst [ms≡]
        [t]         = Indₜ (ctr i j args) d k≡k (ctrᵣ ind∈₁ name≡₁ eq ps)
        [t′]        = Indₜ (ctr i j args′) d′ k′≡k′ (ctrᵣ ind∈₂ name≡₂ eq′ ps′)
        [t≡t′]      = Indₜ₌ (ctr i j args) (ctr i j args′) d₁ d₁′ k₁≡k₁′
                            (ctrᵣ ind∈₃ name≡₃ eq₃ aa)
        ⊢P          = escape [P∙]
        ⊢P′         = escape [P′∙]
        ⊢ctr        = _⊢_:⇒*:_∷_^_.⊢u d
        ⊢ctr′       = _⊢_:⇒*:_∷_^_.⊢u d′
        [aa]        = argsRedEq ⊢Δ (ctrArgInds ind∈ eq) ps ps′ aa
        [args]      = argFst [aa]
        [args′]     = argSnd [aa]
        ⊢args       = escapeArgs [args]
        ⊢args′      = escapeArgs [args′]
        [k]         = Indₜ (ctr i j args) (idRedTerm:*: ⊢ctr) k≡k (ctrᵣ ind∈₁ name≡₁ eq ps)
        [k′]        = Indₜ (ctr i j args′) (idRedTerm:*: ⊢ctr′) k′≡k′ (ctrᵣ ind∈₂ name≡₂ eq′ ps′)
        [t≡k]       = proj₂ (redSubst*Term (redₜ d) [Ind] [k])
        [t′≡k′]     = proj₂ (redSubst*Term (redₜ d′) [Ind] [k′])
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
        [E]         = proj₁ (appsMethod {j = j} {P = P} [args] [Tⱼ] [mⱼ] [ihs])
        [e]′        = irrelevanceTerm [E] [Pk]
                        (proj₂ (appsMethod {j = j} {P = P} [args] [Tⱼ] [mⱼ] [ihs]))
        [E′]        = proj₁ (appsMethod {j = j} {P = P′} [args′] [T′ⱼ] [m′ⱼ] [ihs′])
        [e′]′       = irrelevanceTerm [E′] [P′k′]
                        (proj₂ (appsMethod {j = j} {P = P′} [args′] [T′ⱼ] [m′ⱼ] [ihs′]))
        [e≡e′]      = convEqTerm₂ [Pt] [Pk] [Pt≡Pk]
                        (appsMethod-cong {j = j} {P = P} [aa]
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
                   (Indₜ _ d _ (ctrᵣ _ _ _ _)) _
                   (Indₜ₌ _ _ d₁ _ _ (ne (neNfₜ₌ neK₁ _ _))) =
    ⊥-elim (ctr≢ne neK₁ (whrDet*Term (redₜ d , ctrₙ) (redₜ d₁ , ne neK₁)))
  IndRect-congTerm {rG = !} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   _ (Indₜ _ d′ _ (ctrᵣ _ _ _ _))
                   (Indₜ₌ _ _ _ d₁′ _ (ne (neNfₜ₌ _ neK₁′ _))) =
    ⊥-elim (ctr≢ne neK₁′ (whrDet*Term (redₜ d′ , ctrₙ) (redₜ d₁′ , ne neK₁′)))
  IndRect-congTerm {rG = !} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   (Indₜ _ d _ (ne (neNfₜ neK _ _))) _
                   (Indₜ₌ _ _ d₁ _ _ (ctrᵣ _ _ _ _)) =
    ⊥-elim (ctr≢ne neK (whrDet*Term (redₜ d₁ , ctrₙ) (redₜ d , ne neK)))
  IndRect-congTerm {rG = !} rGlG ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                   ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                   _ (Indₜ _ d′ _ (ne (neNfₜ neK′ _ _)))
                   (Indₜ₌ _ _ _ d₁′ _ (ctrᵣ _ _ _ _)) =
    ⊥-elim (ctr≢ne neK′ (whrDet*Term (redₜ d₁′ , ctrₙ) (redₜ d′ , ne neK′)))

  -- Congruence of the induction hypotheses.
  IndRect-congTerms : ∀ {Δ ind P P′ lG ms ms′ l} {args args′ : List Term} {Ts : List SU.Type}
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
    → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ∷Ind k) args (map emb-stype Ts)
    → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ∷Ind k) args′ (map emb-stype Ts)
    → All₃ (λ a a′ A → ∃ λ k → A PE.≡ Ind k × Δ ⊩Ind a ≡ a′ ∷Ind k) args args′ (map emb-stype Ts)
    → All₃ (λ D u u′ → ∃ λ ([D] : Δ ⊩⟨ l ⟩ D ^ [ ! , ι lG ])
                         → (Δ ⊩⟨ l ⟩ u ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u′ ∷ D ^ [ ! , ι lG ] / [D])
                         × (Δ ⊩⟨ l ⟩ u ≡ u′ ∷ D ^ [ ! , ι lG ] / [D]))
           (map (λ a → P [ a ]) (ctrRecArgs (SU.SInd.name ind) Ts args))
           (map (λ a → IndRect (SU.SInd.name ind) lG P a ms) (ctrRecArgs (SU.SInd.name ind) Ts args))
           (map (λ a → IndRect (SU.SInd.name ind) lG P′ a ms′) (ctrRecArgs (SU.SInd.name ind) Ts args′))
  IndRect-congTerms {Ts = []ₗ} ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                    ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡] []ₐ []ₐ []ₐ = []ₐ
  IndRect-congTerms {ind = ind} {Ts = T ∷ₗ Ts} ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                    ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡]
                    ((k , A≡ , [a]) ∷ₐ ps) ((k′ , A≡′ , [a′]) ∷ₐ ps′)
                    ((k″ , A≡″ , [a≡a′]) ∷ₐ pps)
    with SU.ctrArgIsRecursive (SU.SInd.name ind) T in e
  ... | false = IndRect-congTerms ⊢Δ ind∈ [P∙] [P′∙] [P≡P′∙] [Pu] [Pu≡] [P′u] [P′u≡] [PP′u]
                  ⊢ms ⊢ms′ ⊢ms≡ [ms′] [ms≡] ps ps′ pps
  ... | true with rec-Ind (SU.SInd.name ind) T e
  ...   | PE.refl with A≡ | A≡′ | A≡″
  ...     | PE.refl | PE.refl | PE.refl =
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
                         (Indᵣ {l = l} (idRed:*: (univ (Indⱼ ⊢Δ ind∈))))
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
  ⟦Ind⟧ ⊢Δ₁ = Indᵣ {l = l} (idRed:*: (univ (Indⱼ ⊢Δ₁ ind∈)))

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

-- Validity of the reduct of IndRect on a constructor: the j-th method applied
-- to the constructor arguments and to their induction hypotheses.
IndRect-ctr-rhsᵛ : ∀ {Γ ind j P lG args ms m Ts l}
                 → ([Γ] : ⊩ᵛ Γ)
                 → (ind∈ : ind ∈ₗ senv)
                 → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
                 → ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
                 → ([args] : All₂ (λ a A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                                         → Γ ⊩ᵛ⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A])
                              args (map emb-stype Ts))
                 → ([Pd] : Γ ⊩ᵛ⟨ l ⟩ P [ ctr (SU.SInd.name ind) j args ] ^ [ ! , ι lG ] / [Γ])
                 → SU.ctrArgsTypeList ind j PE.≡ just Ts
                 → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
                 → Γ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
                 → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι lG ] / [Γ])
                                 → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ ! , ι lG ] / [Γ] / [A])
                        ms (indRectBranchTyList ind P ! lG)
                 → nth ms j PE.≡ just m
                 → Γ ⊩ᵛ⟨ l ⟩ apps lG m
                                      (args ++ map (λ a → IndRect (SU.SInd.name ind) lG P a ms)
                                                   (ctrRecArgs (SU.SInd.name ind) Ts args))
                            ∷ P [ ctr (SU.SInd.name ind) j args ] ^ [ ! , ι lG ] / [Γ] / [Pd]
IndRect-ctr-rhsᵛ {Γ = Γ} {ind = ind} {j = j} {P = P} {lG = lG} {args = args} {ms = ms}
                 {m = m} {Ts = Ts} {l = l}
                 [Γ] ind∈ [Ind] [P] [args] [Pd] eq ⊢args ⊢ms [ms] nth≡ {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let i      = SU.SInd.name ind
      psσ    = ⟦args⟧ ⊢Δ [σ] pos [args]
      ⊢msσ   = escapeMethodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms]
      [msσ]  = methodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms]
      nthTy  = nth-map (λ jTs → indRectBranchTy i (proj₁ jTs) (proj₂ jTs)
                                  (subst (liftSubst σ) P) ! lG)
                 (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) j
                 (nth-zip-range (SU.SInd.ctrArgsTypes ind) j eq)
      nthmσ  = nth-map (subst σ) ms j nth≡
      [Tⱼ]   = proj₁ (nthAll₂ [msσ] j nthTy nthmσ)
      [mⱼ]   = proj₂ (nthAll₂ [msσ] j nthTy nthmσ)
      [ihs]  = IndRectTerms ⊢Δ ind∈ (P∙ ⊢Δ [σ]) (Pu ⊢Δ [σ]) (Pu≡ ⊢Δ [σ]) ⊢msσ [msσ] psσ
      [argsσ] = argsRed ⊢Δ inds psσ
      [E]    = proj₁ (appsMethod {j = j} {P = subst (liftSubst σ) P}
                        [argsσ] [Tⱼ] [mⱼ] [ihs])
      [e]    = proj₂ (appsMethod {j = j} {P = subst (liftSubst σ) P}
                        [argsσ] [Tⱼ] [mⱼ] [ihs])
      [res]  = irrelevanceTerm′ (eqPrf σ) PE.refl PE.refl [E] (proj₁ ([Pd] ⊢Δ [σ])) [e]
  in  PE.subst (λ x → Δ ⊩⟨ l ⟩ x ∷ subst σ (P [ ctr i j args ]) ^ [ ! , ι lG ]
                        / proj₁ ([Pd] ⊢Δ [σ]))
               (PE.sym (subst-IndRect-ctr-rhs σ i Ts lG P m args ms)) [res]
    , (λ {σ′} [σ′] [σ≡σ′] →
         let i      = SU.SInd.name ind
             psσ    = ⟦args⟧ ⊢Δ [σ] pos [args]
             psσ′   = ⟦args⟧ ⊢Δ [σ′] pos [args]
             aaσ≡   = ⟦args≡⟧ ⊢Δ [σ] [σ′] [σ≡σ′] pos [args]
             [aaσ]  = argsRedEq ⊢Δ inds psσ psσ′ aaσ≡
             ⊢msσ   = escapeMethodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms]
             ⊢msσ′  = escapeMethodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ′] [ms]
             ⊢msσ≡  = escapeMethodsσ≡ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [ms]
             [msσ]  = methodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms]
             [msσ′] = methodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ′] [ms]
             [msσ≡] = methodsσ≡ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [ms]
             nthTy  = nth-map (λ jTs → indRectBranchTy i (proj₁ jTs) (proj₂ jTs)
                                         (subst (liftSubst σ) P) ! lG)
                        (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) j
                        (nth-zip-range (SU.SInd.ctrArgsTypes ind) j eq)
             nthmσ  = nth-map (subst σ) ms j nth≡
             nthmσ′ = nth-map (subst σ′) ms j nth≡
             mⱼ≡    = nthAll₃ [msσ≡] j nthTy nthmσ nthmσ′
             [Tⱼ]   = proj₁ mⱼ≡
             [mⱼ]   = proj₁ (proj₂ mⱼ≡)
             [mⱼ≡]  = proj₂ (proj₂ (proj₂ mⱼ≡))
             [ihs]  = IndRectTerms ⊢Δ ind∈ (P∙ ⊢Δ [σ]) (Pu ⊢Δ [σ]) (Pu≡ ⊢Δ [σ]) ⊢msσ [msσ] psσ
             [ihs≡] = IndRect-congTerms ⊢Δ ind∈ (P∙ ⊢Δ [σ]) (P∙ ⊢Δ [σ′])
                        (P∙≡ ⊢Δ [σ] [σ′] [σ≡σ′]) (Pu ⊢Δ [σ]) (Pu≡ ⊢Δ [σ])
                        (Pu ⊢Δ [σ′]) (Pu≡ ⊢Δ [σ′]) (PP′u ⊢Δ [σ] [σ′] [σ≡σ′])
                        ⊢msσ ⊢msσ′ ⊢msσ≡ [msσ′] [msσ≡] psσ psσ′ aaσ≡
             [E]    = proj₁ (appsMethod {j = j} {P = subst (liftSubst σ) P}
                               (argFst [aaσ]) [Tⱼ] [mⱼ] [ihs])
             [res]  = irrelevanceEqTerm′ (eqPrf σ) PE.refl PE.refl [E] (proj₁ ([Pd] ⊢Δ [σ]))
                        (appsMethod-cong {j = j} {P = subst (liftSubst σ) P}
                          [aaσ] [Tⱼ] [mⱼ] [mⱼ≡] [ihs≡] [E])
         in  PE.subst₂ (λ x y → Δ ⊩⟨ l ⟩ x ≡ y ∷ subst σ (P [ ctr i j args ]) ^ [ ! , ι lG ]
                                  / proj₁ ([Pd] ⊢Δ [σ]))
                       (PE.sym (subst-IndRect-ctr-rhs σ i Ts lG P m args ms))
                       (PE.sym (subst-IndRect-ctr-rhs σ′ i Ts lG P m args ms)) [res])
  where
  -- The inductive type, the constructor arguments and the motive read off
  -- [Ind] / [args] / [P] at an arbitrary substitution (as in IndRectᵛ).
  ⟦Ind⟧ : ∀ {Δ₁} (⊢Δ₁ : ⊢ Δ₁) → Δ₁ ⊩⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
  ⟦Ind⟧ ⊢Δ₁ = Indᵣ {l = l} (idRed:*: (univ (Indⱼ ⊢Δ₁ ind∈)))

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

  pos : All (SU.isPositive (SU.SInd.name ind)) Ts
  pos = all∈ (SU.ctrArgsTypesPositive ind j Ts eq)

  inds : All (SU.indsInSEnv senv) Ts
  inds = ctrArgInds ind∈ eq

  -- Constructor arguments are all at inductive types, by positivity.
  ⟦args⟧ : ∀ {Δ₁ σ₁ Ts′ as} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
         → All (SU.isPositive (SU.SInd.name ind)) Ts′
         → All₂ (λ a A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                           → Γ ⊩ᵛ⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A])
                as (map emb-stype Ts′)
         → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Δ₁ ⊩Ind a ∷Ind k)
                (map (subst σ₁) as) (map emb-stype Ts′)
  ⟦args⟧ {Ts′ = []ₗ} ⊢Δ₁ [σ₁] []ₐ []ₐ = []ₐ
  ⟦args⟧ {Ts′ = SU.Ind k ∷ₗ Ts′} ⊢Δ₁ [σ₁] (_ ∷ₐ ps) (([A] , [a]) ∷ₐ as) =
    let [A]σ = proj₁ ([A] ⊢Δ₁ [σ₁])
    in  (k , PE.refl , irrelevanceTerm [A]σ (Indᵣ {l = l} (idRed:*: (escape [A]σ))) (proj₁ ([a] ⊢Δ₁ [σ₁])))
        ∷ₐ ⟦args⟧ ⊢Δ₁ [σ₁] ps as
  ⟦args⟧ {Ts′ = SU.Arrow _ _ ∷ₗ Ts′} ⊢Δ₁ [σ₁] (() ∷ₐ ps) _

  ⟦args≡⟧ : ∀ {Δ₁ σ₁ σ₂ Ts′ as} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
              ([σ₂] : Δ₁ ⊩ˢ σ₂ ∷ Γ / [Γ] / ⊢Δ₁)
              ([σ₁≡σ₂] : Δ₁ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / [Γ] / ⊢Δ₁ / [σ₁])
          → All (SU.isPositive (SU.SInd.name ind)) Ts′
          → All₂ (λ a A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                            → Γ ⊩ᵛ⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A])
                 as (map emb-stype Ts′)
          → All₃ (λ a a′ A → ∃ λ k → A PE.≡ Ind k × Δ₁ ⊩Ind a ≡ a′ ∷Ind k)
                 (map (subst σ₁) as) (map (subst σ₂) as) (map emb-stype Ts′)
  ⟦args≡⟧ {Ts′ = []ₗ} ⊢Δ₁ [σ₁] [σ₂] [σ₁≡σ₂] []ₐ []ₐ = []ₐ
  ⟦args≡⟧ {Ts′ = SU.Ind k ∷ₗ Ts′} ⊢Δ₁ [σ₁] [σ₂] [σ₁≡σ₂] (_ ∷ₐ ps) (([A] , [a]) ∷ₐ as) =
    let [A]σ = proj₁ ([A] ⊢Δ₁ [σ₁])
    in  (k , PE.refl , irrelevanceEqTerm [A]σ (Indᵣ {l = l} (idRed:*: (escape [A]σ)))
                         (proj₂ ([a] ⊢Δ₁ [σ₁]) [σ₂] [σ₁≡σ₂]))
        ∷ₐ ⟦args≡⟧ ⊢Δ₁ [σ₁] [σ₂] [σ₁≡σ₂] ps as
  ⟦args≡⟧ {Ts′ = SU.Arrow _ _ ∷ₗ Ts′} ⊢Δ₁ [σ₁] [σ₂] [σ₁≡σ₂] (() ∷ₐ ps) _

  P∙ : ∀ {Δ₁ σ₁} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
     → Δ₁ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ subst (liftSubst σ₁) P ^ [ ! , ι lG ]
  P∙ ⊢Δ₁ [σ₁] = proj₁ ([P] (⊢Δ₁ ∙ escape (proj₁ ([Ind] ⊢Δ₁ [σ₁])))
                           (liftSubstS {F = Ind (SU.SInd.name ind)} [Γ] ⊢Δ₁ [Ind] [σ₁]))

  P∙≡ : ∀ {Δ₁ σ₁ σ₂} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
          ([σ₂] : Δ₁ ⊩ˢ σ₂ ∷ Γ / [Γ] / ⊢Δ₁)
          ([σ₁≡σ₂] : Δ₁ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / [Γ] / ⊢Δ₁ / [σ₁])
        → Δ₁ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩
            subst (liftSubst σ₁) P ≡ subst (liftSubst σ₂) P ^ [ ! , ι lG ] / P∙ ⊢Δ₁ [σ₁]
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
     → Δ₁ ⊩⟨ l ⟩ subst (liftSubst σ₁) P [ u ] ^ [ ! , ι lG ]
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
             ^ [ ! , ι lG ] / Pu ⊢Δ₁ [σ₁] [u]
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
            ^ [ ! , ι lG ] / Pu ⊢Δ₁ [σ₁] [u]
  Pu≡ ⊢Δ₁ [σ₁] = PP′u ⊢Δ₁ [σ₁] [σ₁] (reflSubst [Γ] ⊢Δ₁ [σ₁])

  -- The instance of the motive at the constructor, before and after
  -- pushing the substitution inside.
  eqPrf : ∀ σ₁ → subst (liftSubst σ₁) P [ ctr (SU.SInd.name ind) j (map (subst σ₁) args) ]
                 PE.≡ subst σ₁ (P [ ctr (SU.SInd.name ind) j args ])
  eqPrf σ₁ =
    PE.trans (PE.cong (λ t′ → subst (liftSubst σ₁) P [ t′ ])
                      (PE.sym (subst-ctr σ₁ (SU.SInd.name ind) j args)))
      (PE.trans (singleSubstComp (subst σ₁ (ctr (SU.SInd.name ind) j args)) σ₁ P)
                (PE.sym (PE.trans (substCompEq P) (substConcatSingleton′ P))))

------------------------------------------------------------------------
-- Validity of IndRect congruence.

private
  -- The left methods of a valid equality of methods.
  methodsˡ : ∀ {Γ rG lG ms ms′ As l} {[Γ] : ⊩ᵛ Γ}
    → All₃ (λ m m′ A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                         → (Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                         × (Γ ⊩ᵛ⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                         × (Γ ⊩ᵛ⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])) ms ms′ As
    → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                      → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A]) ms As
  methodsˡ []ₐ = []ₐ
  methodsˡ (([A] , [m] , _ , _) ∷ₐ ps) = ([A] , [m]) ∷ₐ methodsˡ ps

  -- Reducible equality of the methods at a substitution.
  methodsEqσ : ∀ {Γ Δ σ ind P rG lG ms ms′ l}
    → ([Γ] : ⊩ᵛ Γ)
    → (⊢Δ : ⊢ Δ)
    → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
    → All₃ (λ m m′ A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                         → (Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                         × (Γ ⊩ᵛ⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                         × (Γ ⊩ᵛ⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A]))
           ms ms′ (indRectBranchTyList ind P rG lG)
    → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                         → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                         × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A]))
           (indRectBranchTyList ind (subst (liftSubst σ) P) rG lG)
           (map (subst σ) ms) (map (subst σ) ms′)
  methodsEqσ {Δ = Δ} {σ = σ} {ind = ind} {P = P} {rG = rG} {lG = lG} {ms = ms} {ms′ = ms′} {l = l}
             [Γ] ⊢Δ [σ] [ms≡] =
    PE.subst (λ As → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                                       → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                                       × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                                       × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A]))
                          As (map (subst σ) ms) (map (subst σ) ms′))
             (subst-indRectBranchTyList σ ind P rG lG)
             (go ms ms′ (indRectBranchTyList ind P rG lG) [ms≡])
    where
      go : ∀ ns ns′ As →
        All₃ (λ m m′ A → ∃ λ ([A] : _ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                           → (_ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                           × (_ ⊩ᵛ⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                           × (_ ⊩ᵛ⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])) ns ns′ As
        → All₃ (λ A m m′ → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ rG , ι lG ])
                            → (Δ ⊩⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [A])
                            × (Δ ⊩⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [A])
                            × (Δ ⊩⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [A]))
               (map (subst σ) As) (map (subst σ) ns) (map (subst σ) ns′)
      go []ₗ []ₗ []ₗ []ₐ = []ₐ
      go (m ∷ₗ ns) (m′ ∷ₗ ns′) (A ∷ₗ As′) (([A] , [m] , [m′] , [m≡]) ∷ₐ ps) =
        (proj₁ ([A] ⊢Δ [σ]) , proj₁ ([m] ⊢Δ [σ]) , proj₁ ([m′] ⊢Δ [σ]) , [m≡] ⊢Δ [σ])
        ∷ₐ go ns ns′ As′ ps

  -- Judgemental equality of the methods at a substitution.
  escapeMethodsEqσ : ∀ {Γ Δ σ ind P rG lG ms ms′ l}
    → ([Γ] : ⊩ᵛ Γ)
    → (⊢Δ : ⊢ Δ)
    → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
    → All₃ (λ m m′ A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                         → (Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                         × (Γ ⊩ᵛ⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                         × (Γ ⊩ᵛ⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A]))
           ms ms′ (indRectBranchTyList ind P rG lG)
    → Δ ⊢All map (subst σ) ms ≡ map (subst σ) ms′
        ∷ indRectBranchTyList ind (subst (liftSubst σ) P) rG lG ^ [ rG , ι lG ]
  escapeMethodsEqσ {Δ = Δ} {σ = σ} {ind = ind} {P = P} {rG = rG} {lG = lG} {ms = ms} {ms′ = ms′} {l = l}
                   [Γ] ⊢Δ [σ] [ms≡] =
    PE.subst (λ As → Δ ⊢All map (subst σ) ms ≡ map (subst σ) ms′ ∷ As ^ [ rG , ι lG ])
             (subst-indRectBranchTyList σ ind P rG lG)
             (go ms ms′ (indRectBranchTyList ind P rG lG) [ms≡])
    where
      go : ∀ ns ns′ As →
        All₃ (λ m m′ A → ∃ λ ([A] : _ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                           → (_ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                           × (_ ⊩ᵛ⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                           × (_ ⊩ᵛ⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])) ns ns′ As
        → Δ ⊢All map (subst σ) ns ≡ map (subst σ) ns′ ∷ map (subst σ) As ^ [ rG , ι lG ]
      go []ₗ []ₗ []ₗ []ₐ = εⱼ
      go (m ∷ₗ ns) (m′ ∷ₗ ns′) (A ∷ₗ As′) (([A] , [m] , [m′] , [m≡]) ∷ₐ ps) =
        consⱼ (≅ₜ-eq (escapeTermEq (proj₁ ([A] ⊢Δ [σ])) ([m≡] ⊢Δ [σ])))
              (go ns ns′ As′ ps)

IndRect-congᵛ : ∀ {Γ ind P P′ rG lG t t′ ms ms′ l}
              → (rGlG : rG PE.≡ % → lG PE.≡ ⁰)
              → ([Γ] : ⊩ᵛ Γ)
              → (ind∈ : ind ∈ₗ senv)
              → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
              → ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P ^ [ rG , ι lG ] / [Γ] ∙ [Ind])
              → ([P′] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P′ ^ [ rG , ι lG ] / [Γ] ∙ [Ind])
              → ([P≡P′] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ P ≡ P′ ^ [ rG , ι lG ]
                          / [Γ] ∙ [Ind] / [P])
              → ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              → ([t′] : Γ ⊩ᵛ⟨ l ⟩ t′ ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              → ([t≡t′] : Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind])
              → ([Pt] : Γ ⊩ᵛ⟨ l ⟩ P [ t ] ^ [ rG , ι lG ] / [Γ])
              → All₃ (λ m m′ A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                                   → (Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                                   × (Γ ⊩ᵛ⟨ l ⟩ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                                   × (Γ ⊩ᵛ⟨ l ⟩ m ≡ m′ ∷ A ^ [ rG , ι lG ] / [Γ] / [A]))
                     ms ms′ (indRectBranchTyList ind P rG lG)
              → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rG , ι lG ] / [Γ])
                                → Γ ⊩ᵛ⟨ l ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                     ms′ (indRectBranchTyList ind P′ rG lG)
              → Γ ⊩ᵛ⟨ l ⟩ IndRect (SU.SInd.name ind) lG P t ms ≡ IndRect (SU.SInd.name ind) lG P′ t′ ms′
                  ∷ P [ t ] ^ [ rG , ι lG ] / [Γ] / [Pt]
IndRect-congᵛ {Γ = Γ} {ind = ind} {P = P} {P′ = P′} {rG = rG} {lG = lG} {t = t} {t′ = t′}
              {ms = ms} {ms′ = ms′} {l = l}
              rGlG [Γ] ind∈ [Ind] [P] [P′] [P≡P′] [t] [t′] [t≡t′] [Pt] [ms≡] [ms′] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σt]   = ⟦v⟧ {v = t} [t] ⊢Δ [σ]
      [σt′]  = ⟦v⟧ {v = t′} [t′] ⊢Δ [σ]
      [σt≡]  = irrelevanceEqTerm (proj₁ ([Ind] ⊢Δ [σ])) (⟦Ind⟧ ⊢Δ) ([t≡t′] ⊢Δ [σ])
      eqPrf  = PE.trans (singleSubstComp (subst σ t) σ P)
                 (PE.sym (PE.trans (substCompEq P) (substConcatSingleton′ P)))
      [ms]   = methodsˡ [ms≡]
      [res]  = irrelevanceEqTerm′ eqPrf PE.refl PE.refl
                 (Qu {Q = P} [P] ⊢Δ [σ] [σt]) (proj₁ ([Pt] ⊢Δ [σ]))
                 (IndRect-congTerm rGlG ⊢Δ ind∈ (Q∙ {Q = P} [P] ⊢Δ [σ]) (Q∙ {Q = P′} [P′] ⊢Δ [σ])
                    ([P≡P′] (⊢Δ ∙ escape (proj₁ ([Ind] ⊢Δ [σ])))
                            (liftSubstS {F = Ind (SU.SInd.name ind)} [Γ] ⊢Δ [Ind] [σ]))
                    (Qu {Q = P} [P] ⊢Δ [σ]) (Qu≡ {Q = P} [P] ⊢Δ [σ]) (Qu {Q = P′} [P′] ⊢Δ [σ]) (Qu≡ {Q = P′} [P′] ⊢Δ [σ])
                    (PP′u ⊢Δ [σ])
                    (escapeMethodsσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms])
                    (escapeMethodsσ {ind = ind} {P = P′} [Γ] ⊢Δ [σ] [ms′])
                    (escapeMethodsEqσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms≡])
                    (methodsσ {ind = ind} {P = P′} [Γ] ⊢Δ [σ] [ms′])
                    (methodsEqσ {ind = ind} {P = P} [Γ] ⊢Δ [σ] [ms≡])
                    [σt] [σt′] [σt≡])
  in  PE.subst₂ (λ x y → Δ ⊩⟨ l ⟩ x ≡ y ∷ subst σ (P [ t ]) ^ [ rG , ι lG ] / proj₁ ([Pt] ⊢Δ [σ]))
                (PE.sym (subst-IndRect σ (SU.SInd.name ind) lG P t ms))
                (PE.sym (subst-IndRect σ (SU.SInd.name ind) lG P′ t′ ms′)) [res]
  where
  -- The inductive type and the motives read off [Ind] / [P] / [P′] at an
  -- arbitrary substitution (as in IndRectᵛ, for any valid motive Q).
  ⟦Ind⟧ : ∀ {Δ₁} (⊢Δ₁ : ⊢ Δ₁) → Δ₁ ⊩⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
  ⟦Ind⟧ ⊢Δ₁ = Indᵣ {l = l} (idRed:*: (univ (Indⱼ ⊢Δ₁ ind∈)))

  ⟦v⟧ : ∀ {v Δ₁ σ₁} → Γ ⊩ᵛ⟨ l ⟩ v ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind]
      → (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
      → Δ₁ ⊩Ind subst σ₁ v ∷Ind SU.SInd.name ind
  ⟦v⟧ [v] ⊢Δ₁ [σ₁] = irrelevanceTerm (proj₁ ([Ind] ⊢Δ₁ [σ₁])) (⟦Ind⟧ ⊢Δ₁)
                       (proj₁ ([v] ⊢Δ₁ [σ₁]))

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

  Q∙ : ∀ {Q Δ₁ σ₁}
     → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ Q ^ [ rG , ι lG ] / [Γ] ∙ [Ind]
     → (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
     → Δ₁ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩⟨ l ⟩ subst (liftSubst σ₁) Q ^ [ rG , ι lG ]
  Q∙ [Q] ⊢Δ₁ [σ₁] = proj₁ ([Q] (⊢Δ₁ ∙ escape (proj₁ ([Ind] ⊢Δ₁ [σ₁])))
                               (liftSubstS {F = Ind (SU.SInd.name ind)} [Γ] ⊢Δ₁ [Ind] [σ₁]))

  Qu : ∀ {Q Δ₁ σ₁ u}
     → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ Q ^ [ rG , ι lG ] / [Γ] ∙ [Ind]
     → (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
     → Δ₁ ⊩Ind u ∷Ind SU.SInd.name ind
     → Δ₁ ⊩⟨ l ⟩ subst (liftSubst σ₁) Q [ u ] ^ [ rG , ι lG ]
  Qu {Q = Q} {σ₁ = σ₁} {u = u} [Q] ⊢Δ₁ [σ₁] [u] =
    irrelevance′ (PE.sym (singleSubstComp u σ₁ Q))
      (proj₁ ([Q] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u])))

  Qu≡ : ∀ {Q Δ₁ σ₁}
      → ([Q] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ Q ^ [ rG , ι lG ] / [Γ] ∙ [Ind])
      → (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
      → ∀ {u u′} ([u] : Δ₁ ⊩Ind u ∷Ind SU.SInd.name ind)
          ([u′] : Δ₁ ⊩Ind u′ ∷Ind SU.SInd.name ind)
      → Δ₁ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
      → Δ₁ ⊩⟨ l ⟩ subst (liftSubst σ₁) Q [ u ] ≡ subst (liftSubst σ₁) Q [ u′ ]
          ^ [ rG , ι lG ] / Qu {Q = Q} [Q] ⊢Δ₁ [σ₁] [u]
  Qu≡ {Q = Q} {σ₁ = σ₁} [Q] ⊢Δ₁ [σ₁] {u} {u′} [u] [u′] [u≡u′] =
    irrelevanceEq″ (PE.sym (singleSubstComp u σ₁ Q)) (PE.sym (singleSubstComp u′ σ₁ Q))
      PE.refl PE.refl
      (proj₁ ([Q] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u]))) (Qu {Q = Q} [Q] ⊢Δ₁ [σ₁] [u])
      (proj₂ ([Q] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u]))
             ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u′])
             (reflSubst [Γ] ⊢Δ₁ [σ₁] , ⟦u≡⟧ ⊢Δ₁ [σ₁] [u≡u′]))

  -- P [ u ] ≡ P′ [ u ] by the equality of the motives, then P′ [ u ] ≡ P′ [ u′ ].
  PP′u : ∀ {Δ₁ σ₁} (⊢Δ₁ : ⊢ Δ₁) ([σ₁] : Δ₁ ⊩ˢ σ₁ ∷ Γ / [Γ] / ⊢Δ₁)
           {u u′} ([u] : Δ₁ ⊩Ind u ∷Ind SU.SInd.name ind)
           ([u′] : Δ₁ ⊩Ind u′ ∷Ind SU.SInd.name ind)
         → Δ₁ ⊩Ind u ≡ u′ ∷Ind SU.SInd.name ind
         → Δ₁ ⊩⟨ l ⟩ subst (liftSubst σ₁) P [ u ] ≡ subst (liftSubst σ₁) P′ [ u′ ]
             ^ [ rG , ι lG ] / Qu {Q = P} [P] ⊢Δ₁ [σ₁] [u]
  PP′u {σ₁ = σ₁} ⊢Δ₁ [σ₁] {u} {u′} [u] [u′] [u≡u′] =
    transEq (Qu {Q = P} [P] ⊢Δ₁ [σ₁] [u]) (Qu {Q = P′} [P′] ⊢Δ₁ [σ₁] [u]) (Qu {Q = P′} [P′] ⊢Δ₁ [σ₁] [u′])
      (irrelevanceEq″ (PE.sym (singleSubstComp u σ₁ P)) (PE.sym (singleSubstComp u σ₁ P′))
         PE.refl PE.refl
         (proj₁ ([P] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u]))) (Qu {Q = P} [P] ⊢Δ₁ [σ₁] [u])
         ([P≡P′] ⊢Δ₁ ([σ₁] , ⟦u⟧ ⊢Δ₁ [σ₁] [u])))
      (Qu≡ {Q = P′} [P′] ⊢Δ₁ [σ₁] [u] [u′] [u≡u′])

------------------------------------------------------------------------
