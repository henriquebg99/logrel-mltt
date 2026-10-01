import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.IndRectBranch (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}

open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.LogicalRelation senv swf equivs
open import Definition.LogicalRelation.Irrelevance senv swf equivs
open import Definition.LogicalRelation.Properties senv swf equivs
open import Definition.LogicalRelation.Substitution senv swf equivs
open import Definition.LogicalRelation.Substitution.Conversion senv swf equivs
open import Definition.LogicalRelation.Substitution.Reflexivity senv swf equivs
open import Definition.LogicalRelation.Substitution.Escape senv swf equivs
open import Definition.LogicalRelation.Substitution.Weakening senv swf equivs
import Definition.LogicalRelation.Substitution.Irrelevance senv swf equivs as S
open import Definition.LogicalRelation.Substitution.Introductions.Pi senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Ind senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.IndRect senv swf equivs {{eqrel}}
  using (ctrArity; branchTy-nf; Πarg; Πih; ihFun; ihGo; ctrVars; concl; varIdx; rec-Ind)
open import Definition.LogicalRelation.Fundamental.Variable senv swf equivs
open import Tools.Nat
open import Tools.Product
open import Tools.List using (List; All; All₂; []ₐ; _∷ₐ_; map; length; range; range-suc; zip; foldr;
                              _∈ₗ_; ∈ₗ-map; all∈; zip-range-nth)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Tools.Maybe using (just)
open import Tools.Inequality using (true; false; filter)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU

-- Validity of the types of the methods of IndRect, and their congruence
-- under a valid equality of the motive.  This follows
-- Definition.Typed.IndRectCong, one level up: the branch types are nested
-- Π-chains whose leaves instantiate the motive as P [ u ]↑^ d, so the
-- validity of the leaves needs the substitutions of the extended context to
-- be cut back to the context of the motive (Dropᵛ below).

-- A valid argument of a constructor, at its own (closed) type.
ValidArg : ∀ {Δ} → ⊩ᵛ Δ → Term → Term → Set
ValidArg {Δ} [Δ] a A = ∃ λ ([A] : Δ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι ⁰ ] / [Δ])
                       → Δ ⊩ᵛ⟨ ∞ ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [Δ] / [A]

-- Forgetting the d innermost components of a substitution.
tail^ : Nat → Subst → Subst
tail^ 0 σ = σ
tail^ (1+ d) σ = tail^ d (tail σ)

-- [Δ] extends [Γ] by d types: valid substitutions of Δ restrict to Γ.
record Dropᵛ {Γ Δ} ([Γ] : ⊩ᵛ Γ) ([Δ] : ⊩ᵛ Δ) (d : Nat) : Set where
  field
    dropˢ  : ∀ {Δ′ σ} (⊢Δ′ : ⊢ Δ′)
           → Δ′ ⊩ˢ σ ∷ Δ / [Δ] / ⊢Δ′
           → Δ′ ⊩ˢ tail^ d σ ∷ Γ / [Γ] / ⊢Δ′
    dropˢ≡ : ∀ {Δ′ σ σ′} (⊢Δ′ : ⊢ Δ′) ([σ] : Δ′ ⊩ˢ σ ∷ Δ / [Δ] / ⊢Δ′)
           → Δ′ ⊩ˢ σ ≡ σ′ ∷ Δ / [Δ] / ⊢Δ′ / [σ]
           → Δ′ ⊩ˢ tail^ d σ ≡ tail^ d σ′ ∷ Γ / [Γ] / ⊢Δ′ / dropˢ ⊢Δ′ [σ]
open Dropᵛ

private
  drop0 : ∀ {Γ} ([Γ] : ⊩ᵛ Γ) → Dropᵛ [Γ] [Γ] 0
  drop0 [Γ] = record { dropˢ = λ ⊢Δ′ [σ] → [σ] ; dropˢ≡ = λ ⊢Δ′ [σ] [σ≡σ′] → [σ≡σ′] }

  drop∙ : ∀ {Γ Δ F rF l d} {[Γ] : ⊩ᵛ Γ} {[Δ] : ⊩ᵛ Δ} ([F] : Δ ⊩ᵛ⟨ l ⟩ F ^ rF / [Δ])
        → Dropᵛ [Γ] [Δ] d → Dropᵛ [Γ] (_∙_ {A = F} [Δ] [F]) (1+ d)
  drop∙ [F] e = record { dropˢ = λ ⊢Δ′ [σ] → dropˢ e ⊢Δ′ (proj₁ [σ])
                       ; dropˢ≡ = λ ⊢Δ′ [σ] [σ≡σ′] → dropˢ≡ e ⊢Δ′ (proj₁ [σ]) (proj₁ [σ≡σ′]) }

  tail^-var : ∀ d σ x → tail^ d σ x PE.≡ σ (d + x)
  tail^-var 0 σ x = PE.refl
  tail^-var (1+ d) σ x = tail^-var d (tail σ) x

  wk1^Subst-var : ∀ d x → wk1^Subst d idSubst x PE.≡ var (d + x)
  wk1^Subst-var 0 x = PE.refl
  wk1^Subst-var (1+ d) x = PE.cong wk1 (wk1^Subst-var d x)

  subst-↑^-var : ∀ d u σ x
               → (σ ₛ•ₛ consSubst (wk1^Subst d idSubst) u) x PE.≡ consSubst (tail^ d σ) (subst σ u) x
  subst-↑^-var d u σ 0 = PE.refl
  subst-↑^-var d u σ (1+ x) =
    PE.trans (PE.cong (subst σ) (wk1^Subst-var d x)) (PE.sym (tail^-var d σ x))

  subst-↑^ : ∀ d P u σ → subst σ (P [ u ]↑^ d) PE.≡ subst (consSubst (tail^ d σ) (subst σ u)) P
  subst-↑^ d P u σ = PE.trans (substCompEq P) (substVar-to-subst (subst-↑^-var d u σ) P)

  -- The motive, instantiated with a valid argument of [Ind i] living [d]
  -- types further out.
  motiveᵛ : ∀ {Γ Δ i P lG u d} ([Γ] : ⊩ᵛ Γ)
            ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
          → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind]
          → ([Δ] : ⊩ᵛ Δ) → Dropᵛ [Γ] [Δ] d
          → ([IndΔ] : Δ ⊩ᵛ⟨ ∞ ⟩ Ind i ^ [ ! , ι ⁰ ] / [Δ])
          → Δ ⊩ᵛ⟨ ∞ ⟩ u ∷ Ind i ^ [ ! , ι ⁰ ] / [Δ] / [IndΔ]
          → Δ ⊩ᵛ⟨ ∞ ⟩ P [ u ]↑^ d ^ [ ! , ι lG ] / [Δ]
  motiveᵛ {P = P} {u = u} {d = d} [Γ] [Ind] [P] [Δ] e [IndΔ] [u] {σ = σ} ⊢Δ′ [σ] =
    let [σΓ] = dropˢ e ⊢Δ′ [σ]
        [σu] = irrelevanceTerm (proj₁ ([IndΔ] ⊢Δ′ [σ])) (proj₁ ([Ind] ⊢Δ′ [σΓ]))
                               (proj₁ ([u] ⊢Δ′ [σ]))
        [Pσ] = proj₁ ([P] ⊢Δ′ ([σΓ] , [σu]))
        [Pσ]′ = irrelevance′ (PE.sym (subst-↑^ d P u σ)) [Pσ]
    in  [Pσ]′
    ,   (λ {σ′} [σ′] [σ≡σ′] →
           let [σ′Γ] = dropˢ e ⊢Δ′ [σ′]
               [σ′u] = irrelevanceTerm (proj₁ ([IndΔ] ⊢Δ′ [σ′])) (proj₁ ([Ind] ⊢Δ′ [σ′Γ]))
                                       (proj₁ ([u] ⊢Δ′ [σ′]))
               [σu≡σ′u] = irrelevanceEqTerm (proj₁ ([IndΔ] ⊢Δ′ [σ])) (proj₁ ([Ind] ⊢Δ′ [σΓ]))
                                            (proj₂ ([u] ⊢Δ′ [σ]) [σ′] [σ≡σ′])
           in  irrelevanceEq″ (PE.sym (subst-↑^ d P u σ)) (PE.sym (subst-↑^ d P u σ′))
                              PE.refl PE.refl [Pσ] [Pσ]′
                              (proj₂ ([P] ⊢Δ′ ([σΓ] , [σu])) ([σ′Γ] , [σ′u])
                                     (dropˢ≡ e ⊢Δ′ [σ] [σ≡σ′] , [σu≡σ′u])))

  motiveEqᵛ : ∀ {Γ Δ i P P′ lG u d} ([Γ] : ⊩ᵛ Γ)
              ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
              ([P] : Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
            → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ≡ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind] / [P]
            → ([Δ] : ⊩ᵛ Δ) (e : Dropᵛ [Γ] [Δ] d)
              ([IndΔ] : Δ ⊩ᵛ⟨ ∞ ⟩ Ind i ^ [ ! , ι ⁰ ] / [Δ])
              ([u] : Δ ⊩ᵛ⟨ ∞ ⟩ u ∷ Ind i ^ [ ! , ι ⁰ ] / [Δ] / [IndΔ])
            → Δ ⊩ᵛ⟨ ∞ ⟩ P [ u ]↑^ d ≡ P′ [ u ]↑^ d ^ [ ! , ι lG ] / [Δ]
                / motiveᵛ {P = P} {u = u} {d = d} [Γ] [Ind] [P] [Δ] e [IndΔ] [u]
  motiveEqᵛ {P = P} {P′} {u = u} {d = d} [Γ] [Ind] [P] [P≡P′] [Δ] e [IndΔ] [u] {σ = σ} ⊢Δ′ [σ] =
    let [σΓ] = dropˢ e ⊢Δ′ [σ]
        [σu] = irrelevanceTerm (proj₁ ([IndΔ] ⊢Δ′ [σ])) (proj₁ ([Ind] ⊢Δ′ [σΓ]))
                               (proj₁ ([u] ⊢Δ′ [σ]))
    in  irrelevanceEq″ (PE.sym (subst-↑^ d P u σ)) (PE.sym (subst-↑^ d P′ u σ)) PE.refl PE.refl
                       (proj₁ ([P] ⊢Δ′ ([σΓ] , [σu])))
                       (proj₁ (motiveᵛ {P = P} {u = u} {d = d} [Γ] [Ind] [P] [Δ] e [IndΔ] [u] ⊢Δ′ [σ]))
                       ([P≡P′] ⊢Δ′ ([σΓ] , [σu]))

  -- The argument types of a constructor are inductive types, by positivity.
  embᵛ : ∀ {i Γ} T → SU.isPositive i T → SU.indsInSEnv senv T → ([Γ] : ⊩ᵛ Γ)
       → Γ ⊩ᵛ⟨ ∞ ⟩ emb-stype T ^ [ ! , ι ⁰ ] / [Γ]
  embᵛ (SU.Ind k) _ k∈ [Γ] = Indᵛ k∈ [Γ]
  embᵛ (SU.Arrow _ _) () _ _

  -- [Γ] extended by the argument types [Ts], grown on the left so that it
  -- follows the recursion of the telescopes below.
  ext : Con Term → List SU.Type → Con Term
  ext Γ []ₗ = Γ
  ext Γ (T ∷ₗ Ts) = ext (Γ ∙ emb-stype T ^ [ ! , ι ⁰ ]) Ts

  extᵛ : ∀ {i Γ} Ts → All (SU.isPositive i) Ts → All (SU.indsInSEnv senv) Ts
       → ⊩ᵛ Γ → ⊩ᵛ ext Γ Ts
  extᵛ []ₗ []ₐ []ₐ [Γ] = [Γ]
  extᵛ {i} (T ∷ₗ Ts) (p ∷ₐ ps) (q ∷ₐ qs) [Γ] = extᵛ {i} Ts ps qs ([Γ] ∙ embᵛ {i} T p q [Γ])

  ext-drop : ∀ {i Γ₀ Γ} Ts d (ps : All (SU.isPositive i) Ts) (qs : All (SU.indsInSEnv senv) Ts)
             ([Γ₀] : ⊩ᵛ Γ₀) ([Γ] : ⊩ᵛ Γ)
           → Dropᵛ [Γ₀] [Γ] d → Dropᵛ [Γ₀] (extᵛ {i} Ts ps qs [Γ]) (length Ts + d)
  ext-drop []ₗ d []ₐ []ₐ [Γ₀] [Γ] e = e
  ext-drop {i} (T ∷ₗ Ts) d (p ∷ₐ ps) (q ∷ₐ qs) [Γ₀] [Γ] e =
    let [T] = embᵛ {i} T p q [Γ]
    in  PE.subst (Dropᵛ [Γ₀] (extᵛ {i} Ts ps qs (_∙_ {A = emb-stype T} [Γ] [T]))) (plusSuc (length Ts) d)
                 (ext-drop {i} Ts (1+ d) ps qs [Γ₀] (_∙_ {A = emb-stype T} [Γ] [T]) (drop∙ [T] e))

  -- Weakening of a valid argument by one hypothesis.
  wkValid : ∀ {Γ F rF a} T ([Γ] : ⊩ᵛ Γ) ([F] : Γ ⊩ᵛ⟨ ∞ ⟩ F ^ rF / [Γ])
          → ValidArg [Γ] a (emb-stype T) → ValidArg (_∙_ {A = F} [Γ] [F]) (wk1 a) (emb-stype T)
  wkValid {F = F} {a = a} T [Γ] [F] ([A] , [a]) =
    PE.subst (ValidArg (_∙_ {A = F} [Γ] [F]) (wk1 a)) (wk-emb-stype (step id) T)
             (wk1ᵛ {A = emb-stype T} {F = F} [Γ] [F] [A] , wk1Termᵛ {F = F} {G = emb-stype T} {t = a} [Γ] [F] [A] [a])

  -- A variable of [Γ], seen in the extension.
  ext-wkVar : ∀ {i Γ} Ts x T (ps : All (SU.isPositive i) Ts) (qs : All (SU.indsInSEnv senv) Ts)
              ([Γ] : ⊩ᵛ Γ)
            → ValidArg [Γ] (var x) (emb-stype T)
            → ValidArg (extᵛ {i} Ts ps qs [Γ]) (var (length Ts + x)) (emb-stype T)
  ext-wkVar []ₗ x T []ₐ []ₐ [Γ] [x] = [x]
  ext-wkVar {i} (S ∷ₗ Ts) x T (p ∷ₐ ps) (q ∷ₐ qs) [Γ] [x] =
    let [S] = embᵛ {i} S p q [Γ]
    in  PE.subst (λ y → ValidArg (extᵛ {i} Ts ps qs (_∙_ {A = emb-stype S} [Γ] [S])) (var y) (emb-stype T))
                 (plusSuc (length Ts) x)
                 (ext-wkVar {i} Ts (1+ x) T ps qs (_∙_ {A = emb-stype S} [Γ] [S]) (wkValid {F = emb-stype S} T [Γ] [S] [x]))

  -- The arguments of the constructor, as the variables of the extension.
  ext-vars : ∀ {i Γ} Ts (ps : All (SU.isPositive i) Ts) (qs : All (SU.indsInSEnv senv) Ts)
             ([Γ] : ⊩ᵛ Γ)
           → All₂ (ValidArg (extᵛ {i} Ts ps qs [Γ]))
                  (map (λ v → var ((length Ts - 1) - v)) (range (length Ts))) (map emb-stype Ts)
  ext-vars []ₗ []ₐ []ₐ [Γ] = []ₐ
  ext-vars {i} (T ∷ₗ Ts) (p ∷ₐ ps) (q ∷ₐ qs) [Γ] =
    let m = length Ts
        [T] = embᵛ {i} T p q [Γ]
        [Γ∙] = _∙_ {A = emb-stype T} [Γ] [T]
        [Δ] = extᵛ {i} Ts ps qs [Γ∙]
    in  PE.subst (λ ts → All₂ (ValidArg [Δ]) ts (map emb-stype (T ∷ₗ Ts)))
          (PE.sym (PE.trans (PE.cong (map (λ v → var (m - v))) (range-suc m))
                            (PE.cong (var m ∷ₗ_)
                              (PE.trans (map-map (λ v → var (m - v)) 1+ (range m))
                                        (map-cong (range m) (λ v → PE.cong var (minus-suc m v)))))))
          (PE.subst (λ y → ValidArg [Δ] (var y) (emb-stype T)) (plusZero m)
                    (ext-wkVar {i} Ts 0 T ps qs [Γ∙]
                      (PE.subst (ValidArg [Γ∙] (var 0)) (wk-emb-stype (step id) T)
                                (fundamentalVar here [Γ∙])))
           ∷ₐ ext-vars {i} Ts ps qs [Γ∙])

  escapeArgsᵛ : ∀ {Δ as As} ([Δ] : ⊩ᵛ Δ) → All₂ (ValidArg [Δ]) as As → Δ ⊢All as ∷ As ^ [ ! , ι ⁰ ]
  escapeArgsᵛ [Δ] []ₐ = εⱼ
  escapeArgsᵛ [Δ] (([A] , [a]) ∷ₐ ps) = consⱼ (escapeTermᵛ [Δ] [A] [a]) (escapeArgsᵛ [Δ] ps)

  -- Weakening of the arguments by one hypothesis.
  wkArgsᵛ : ∀ {Δ F rF} ([Δ] : ⊩ᵛ Δ) ([F] : Δ ⊩ᵛ⟨ ∞ ⟩ F ^ rF / [Δ]) ℓ n (vs : List Nat) Ss
          → All₂ (ValidArg [Δ]) (map (λ v → var (((n - 1) - v) + ℓ)) vs) (map emb-stype Ss)
          → All₂ (ValidArg (_∙_ {A = F} [Δ] [F])) (map (λ v → var (((n - 1) - v) + 1+ ℓ)) vs)
                 (map emb-stype Ss)
  wkArgsᵛ [Δ] [F] ℓ n []ₗ []ₗ []ₐ = []ₐ
  wkArgsᵛ [Δ] [F] ℓ n []ₗ (S ∷ₗ Ss) ()
  wkArgsᵛ [Δ] [F] ℓ n (v ∷ₗ vs) []ₗ ()
  wkArgsᵛ {F = F} [Δ] [F] ℓ n (v ∷ₗ vs) (S ∷ₗ Ss) ([v] ∷ₐ [vs]) =
    PE.subst (λ y → ValidArg (_∙_ {A = F} [Δ] [F]) (var y) (emb-stype S)) (PE.sym (plusSuc ((n - 1) - v) ℓ))
             (wkValid {F = F} S [Δ] [F] [v])
    ∷ₐ wkArgsᵛ {F = F} [Δ] [F] ℓ n vs Ss [vs]

  wkRecᵛ : ∀ {Δ F rF i} ([Δ] : ⊩ᵛ Δ) ([F] : Δ ⊩ᵛ⟨ ∞ ⟩ F ^ rF / [Δ]) ℓ n (rs : List Nat)
         → All (λ r → ValidArg [Δ] (var (((n - 1) - r) + ℓ)) (Ind i)) rs
         → All (λ r → ValidArg (_∙_ {A = F} [Δ] [F]) (var (((n - 1) - r) + 1+ ℓ)) (Ind i)) rs
  wkRecᵛ [Δ] [F] ℓ n []ₗ []ₐ = []ₐ
  wkRecᵛ {F = F} {i = i} [Δ] [F] ℓ n (r ∷ₗ rs) ([r] ∷ₐ [rs]) =
    PE.subst (λ y → ValidArg (_∙_ {A = F} [Δ] [F]) (var y) (Ind i)) (PE.sym (plusSuc ((n - 1) - r) ℓ))
             (wkValid {F = F} (SU.Ind i) [Δ] [F] [r])
    ∷ₐ wkRecᵛ {F = F} [Δ] [F] ℓ n rs [rs]

  -- The recursive arguments are at the inductive type being eliminated.
  recArgsᵛ : ∀ {Δ i} ([Δ] : ⊩ᵛ Δ) (f : Nat → Term) (vs : List Nat) Ss
           → All₂ (ValidArg [Δ]) (map f vs) (map emb-stype Ss)
           → All (λ r → ValidArg [Δ] (f r) (Ind i))
                 (map proj₁ (filter (λ vS → SU.ctrArgIsRecursive i (proj₂ vS)) (zip vs Ss)))
  recArgsᵛ [Δ] f []ₗ []ₗ []ₐ = []ₐ
  recArgsᵛ [Δ] f []ₗ (S ∷ₗ Ss) ()
  recArgsᵛ [Δ] f (v ∷ₗ vs) []ₗ ()
  recArgsᵛ {i = i} [Δ] f (v ∷ₗ vs) (S ∷ₗ Ss) ([v] ∷ₐ [vs])
    with SU.ctrArgIsRecursive i S in e
  ... | false = recArgsᵛ [Δ] f vs Ss [vs]
  ... | true with rec-Ind i S e
  ...   | PE.refl = [v] ∷ₐ recArgsᵛ [Δ] f vs Ss [vs]

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
  teleIhTy : Nat → Nat → List SU.Type → Term → Level → Nat → List Nat → Term
  teleIhTy i j Ts P lG ℓ rs =
    foldr (Πih ! lG) (concl i j P (ctrArity Ts) (length (ctrRecIndices i Ts))) (ihGo (ctrArity Ts) P ℓ rs)

  teleIhᵛ : ∀ {Γ Δ P lG} ind j Ts ℓ (rs : List Nat)
          → ind ∈ₗ senv
          → SU.ctrArgsTypeList ind j PE.≡ just Ts
          → ℓ + length rs PE.≡ length (ctrRecIndices (SU.SInd.name ind) Ts)
          → ([Γ] : ⊩ᵛ Γ)
            ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
          → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind]
          → ([Δ] : ⊩ᵛ Δ)
          → Dropᵛ [Γ] [Δ] (ctrArity Ts + ℓ)
          → All₂ (ValidArg [Δ]) (map (λ v → var (((ctrArity Ts - 1) - v) + ℓ)) (range (ctrArity Ts)))
                 (map emb-stype Ts)
          → All (λ r → ValidArg [Δ] (var (((ctrArity Ts - 1) - r) + ℓ)) (Ind (SU.SInd.name ind))) rs
          → Δ ⊩ᵛ⟨ ∞ ⟩ teleIhTy (SU.SInd.name ind) j Ts P lG ℓ rs ^ [ ! , ι lG ] / [Δ]
  teleIhᵛ {Γ} {Δ} {P} ind j Ts ℓ []ₗ ind∈ eqTs eq [Γ] [Ind] [P] [Δ] e [args] []ₐ
    with PE.trans (PE.sym (plusZero ℓ)) eq
  ... | PE.refl =
    let n = ctrArity Ts
        i = SU.SInd.name ind
        [IndΔ] = Indᵛ {l = ∞} (∈ₗ-map SU.SInd.name ind∈) [Δ]
        [args]′ = PE.subst (λ ts → All₂ (ValidArg [Δ]) ts (map emb-stype Ts))
                    (map-range-cong _ _ n
                      (λ v h → PE.cong var (PE.trans (plus-comm ((n - 1) - v) ℓ) (PE.sym (varIdx ℓ n v h)))))
                    [args]
    in  motiveᵛ {P = P} {u = ctr i j (ctrVars n ℓ)} {d = ℓ + n} [Γ] [Ind] [P] [Δ]
                (PE.subst (Dropᵛ [Γ] [Δ]) (plus-comm n ℓ) e) [IndΔ]
                (ctrᵛ {ind = ind} {j = j} {Ts = Ts} {l = ∞} [Δ] [IndΔ] ind∈ eqTs
                      (escapeArgsᵛ [Δ] [args]′) [args]′)
  teleIhᵛ {Γ} {Δ} {P} {lG} ind j Ts ℓ (r ∷ₗ rs) ind∈ eqTs eq [Γ] [Ind] [P] [Δ] e [args] (([IndΔ] , [r]) ∷ₐ [rs]) =
    let n = ctrArity Ts
        i = SU.SInd.name ind
        [F] = motiveᵛ {P = P} {d = n + ℓ} [Γ] [Ind] [P] [Δ] e [IndΔ] [r]
    in  Πᵛ {F = ihFun n P r ℓ} {G = teleIhTy i j Ts P lG (1+ ℓ) rs}
           (≡is≤ PE.refl) (≡is≤ PE.refl) [Δ] [F]
           (teleIhᵛ ind j Ts (1+ ℓ) rs ind∈ eqTs (PE.trans (PE.sym (plusSuc ℓ (length rs))) eq)
                    [Γ] [Ind] [P] (_∙_ {A = ihFun n P r ℓ} [Δ] [F])
                    (PE.subst (Dropᵛ [Γ] (_∙_ {A = ihFun n P r ℓ} [Δ] [F])) (PE.sym (plusSuc n ℓ)) (drop∙ [F] e))
                    (wkArgsᵛ {F = ihFun n P r ℓ} [Δ] [F] ℓ n (range n) Ts [args])
                    (wkRecᵛ {F = ihFun n P r ℓ} [Δ] [F] ℓ n rs [rs]))

  teleIhEqᵛ : ∀ {Γ Δ P P′ lG} ind j Ts ℓ (rs : List Nat)
            → (ind∈ : ind ∈ₗ senv)
            → (eqTs : SU.ctrArgsTypeList ind j PE.≡ just Ts)
            → ℓ + length rs PE.≡ length (ctrRecIndices (SU.SInd.name ind) Ts)
            → ([Γ] : ⊩ᵛ Γ)
              ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
              ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
              ([P′] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
            → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ≡ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind] / [P]
            → ([Δ] : ⊩ᵛ Δ)
            → Dropᵛ [Γ] [Δ] (ctrArity Ts + ℓ)
            → All₂ (ValidArg [Δ]) (map (λ v → var (((ctrArity Ts - 1) - v) + ℓ)) (range (ctrArity Ts)))
                   (map emb-stype Ts)
            → All (λ r → ValidArg [Δ] (var (((ctrArity Ts - 1) - r) + ℓ)) (Ind (SU.SInd.name ind))) rs
            → ([A] : Δ ⊩ᵛ⟨ ∞ ⟩ teleIhTy (SU.SInd.name ind) j Ts P lG ℓ rs ^ [ ! , ι lG ] / [Δ])
            → Δ ⊩ᵛ⟨ ∞ ⟩ teleIhTy (SU.SInd.name ind) j Ts P lG ℓ rs
                      ≡ teleIhTy (SU.SInd.name ind) j Ts P′ lG ℓ rs ^ [ ! , ι lG ] / [Δ] / [A]
  teleIhEqᵛ {Γ} {Δ} {P} {P′} ind j Ts ℓ []ₗ ind∈ eqTs eq [Γ] [Ind] [P] [P′] [P≡P′] [Δ] e [args] []ₐ [A]
    with PE.trans (PE.sym (plusZero ℓ)) eq
  ... | PE.refl =
    let n = ctrArity Ts
        i = SU.SInd.name ind
        [IndΔ] = Indᵛ {l = ∞} (∈ₗ-map SU.SInd.name ind∈) [Δ]
        [args]′ = PE.subst (λ ts → All₂ (ValidArg [Δ]) ts (map emb-stype Ts))
                    (map-range-cong _ _ n
                      (λ v h → PE.cong var (PE.trans (plus-comm ((n - 1) - v) ℓ) (PE.sym (varIdx ℓ n v h)))))
                    [args]
        e′ = PE.subst (Dropᵛ [Γ] [Δ]) (plus-comm n ℓ) e
        [u] = ctrᵛ {ind = ind} {j = j} {Ts = Ts} {l = ∞} [Δ] [IndΔ] ind∈ eqTs
                   (escapeArgsᵛ [Δ] [args]′) [args]′
    in  S.irrelevanceEq {A = concl i j P n ℓ} {B = concl i j P′ n ℓ} [Δ] [Δ]
          (motiveᵛ {P = P} {u = ctr i j (ctrVars n ℓ)} {d = ℓ + n} [Γ] [Ind] [P] [Δ] e′ [IndΔ] [u])
          [A]
          (motiveEqᵛ {P = P} {P′} {u = ctr i j (ctrVars n ℓ)} {d = ℓ + n} [Γ] [Ind] [P] [P≡P′] [Δ] e′ [IndΔ] [u])
  teleIhEqᵛ {Γ} {Δ} {P} {P′} {lG} ind j Ts ℓ (r ∷ₗ rs) ind∈ eqTs eq [Γ] [Ind] [P] [P′] [P≡P′] [Δ] e [args]
            (([IndΔ] , [r]) ∷ₐ [rs]) [A] =
    let n = ctrArity Ts
        i = SU.SInd.name ind
        eq′ = PE.trans (PE.sym (plusSuc ℓ (length rs))) eq
        [F] = motiveᵛ {P = P} {d = n + ℓ} [Γ] [Ind] [P] [Δ] e [IndΔ] [r]
        [H] = motiveᵛ {P = P′} {d = n + ℓ} [Γ] [Ind] [P′] [Δ] e [IndΔ] [r]
        e∙ : ∀ {F rF} ([F] : Δ ⊩ᵛ⟨ ∞ ⟩ F ^ rF / [Δ]) → Dropᵛ [Γ] (_∙_ {A = F} [Δ] [F]) (n + 1+ ℓ)
        e∙ {F} [F] = PE.subst (Dropᵛ [Γ] (_∙_ {A = F} [Δ] [F])) (PE.sym (plusSuc n ℓ)) (drop∙ [F] e)
        [G] = teleIhᵛ {P = P} ind j Ts (1+ ℓ) rs ind∈ eqTs eq′ [Γ] [Ind] [P] (_∙_ {A = ihFun n P r ℓ} [Δ] [F]) (e∙ [F])
                      (wkArgsᵛ {F = ihFun n P r ℓ} [Δ] [F] ℓ n (range n) Ts [args]) (wkRecᵛ {F = ihFun n P r ℓ} [Δ] [F] ℓ n rs [rs])
        [E] = teleIhᵛ {P = P′} ind j Ts (1+ ℓ) rs ind∈ eqTs eq′ [Γ] [Ind] [P′] (_∙_ {A = ihFun n P′ r ℓ} [Δ] [H]) (e∙ [H])
                      (wkArgsᵛ {F = ihFun n P′ r ℓ} [Δ] [H] ℓ n (range n) Ts [args]) (wkRecᵛ {F = ihFun n P′ r ℓ} [Δ] [H] ℓ n rs [rs])
        [G≡E] = teleIhEqᵛ {P = P} {P′} ind j Ts (1+ ℓ) rs ind∈ eqTs eq′ [Γ] [Ind] [P] [P′] [P≡P′]
                          (_∙_ {A = ihFun n P r ℓ} [Δ] [F]) (e∙ [F])
                          (wkArgsᵛ {F = ihFun n P r ℓ} [Δ] [F] ℓ n (range n) Ts [args]) (wkRecᵛ {F = ihFun n P r ℓ} [Δ] [F] ℓ n rs [rs]) [G]
    in  S.irrelevanceEq {A = teleIhTy i j Ts P lG ℓ (r ∷ₗ rs)} {B = teleIhTy i j Ts P′ lG ℓ (r ∷ₗ rs)}
          [Δ] [Δ]
          (Πᵛ {F = ihFun n P r ℓ} {G = teleIhTy i j Ts P lG (1+ ℓ) rs}
              (≡is≤ PE.refl) (≡is≤ PE.refl) [Δ] [F] [G])
          [A]
          (Π-congᵛ {F = ihFun n P r ℓ} {G = teleIhTy i j Ts P lG (1+ ℓ) rs}
                   {H = ihFun n P′ r ℓ} {E = teleIhTy i j Ts P′ lG (1+ ℓ) rs}
                   (≡is≤ PE.refl) (≡is≤ PE.refl) [Δ] [F] [G] [H] [E]
                   (motiveEqᵛ {P = P} {P′} {d = n + ℓ} [Γ] [Ind] [P] [P≡P′] [Δ] e [IndΔ] [r])
                   [G≡E])

  -- The telescope of the arguments of the constructor.
  teleArgᵛ : ∀ {i Γ lG Z} Ts (ps : All (SU.isPositive i) Ts) (qs : All (SU.indsInSEnv senv) Ts)
             ([Γ] : ⊩ᵛ Γ)
           → ext Γ Ts ⊩ᵛ⟨ ∞ ⟩ Z ^ [ ! , ι lG ] / extᵛ {i} Ts ps qs [Γ]
           → Γ ⊩ᵛ⟨ ∞ ⟩ foldr (Πarg ! lG) Z (map emb-stype Ts) ^ [ ! , ι lG ] / [Γ]
  teleArgᵛ []ₗ []ₐ []ₐ [Γ] [Z] = [Z]
  teleArgᵛ {i} {lG = lG} {Z} (T ∷ₗ Ts) (p ∷ₐ ps) (q ∷ₐ qs) [Γ] [Z] =
    let [T] = embᵛ {i} T p q [Γ]
    in  Πᵛ {F = emb-stype T} {G = foldr (Πarg ! lG) Z (map emb-stype Ts)}
           (⁰min lG) (≡is≤ PE.refl) [Γ] [T] (teleArgᵛ {i} {Z = Z} Ts ps qs (_∙_ {A = emb-stype T} [Γ] [T]) [Z])

  teleArgEqᵛ : ∀ {i Γ lG Z Z′} Ts (ps : All (SU.isPositive i) Ts) (qs : All (SU.indsInSEnv senv) Ts)
               ([Γ] : ⊩ᵛ Γ)
               ([Z] : ext Γ Ts ⊩ᵛ⟨ ∞ ⟩ Z ^ [ ! , ι lG ] / extᵛ {i} Ts ps qs [Γ])
               ([Z′] : ext Γ Ts ⊩ᵛ⟨ ∞ ⟩ Z′ ^ [ ! , ι lG ] / extᵛ {i} Ts ps qs [Γ])
             → ext Γ Ts ⊩ᵛ⟨ ∞ ⟩ Z ≡ Z′ ^ [ ! , ι lG ] / extᵛ {i} Ts ps qs [Γ] / [Z]
             → Γ ⊩ᵛ⟨ ∞ ⟩ foldr (Πarg ! lG) Z (map emb-stype Ts)
                       ≡ foldr (Πarg ! lG) Z′ (map emb-stype Ts) ^ [ ! , ι lG ] / [Γ]
                       / teleArgᵛ {i} {Z = Z} Ts ps qs [Γ] [Z]
  teleArgEqᵛ []ₗ []ₐ []ₐ [Γ] [Z] [Z′] [Z≡Z′] = [Z≡Z′]
  teleArgEqᵛ {i} {lG = lG} {Z} {Z′} (T ∷ₗ Ts) (p ∷ₐ ps) (q ∷ₐ qs) [Γ] [Z] [Z′] [Z≡Z′] =
    let [T] = embᵛ {i} T p q [Γ]
    in  Π-congᵛ {F = emb-stype T} {G = foldr (Πarg ! lG) Z (map emb-stype Ts)}
                {H = emb-stype T} {E = foldr (Πarg ! lG) Z′ (map emb-stype Ts)}
                (⁰min lG) (≡is≤ PE.refl) [Γ] [T]
                (teleArgᵛ {i} {Z = Z} Ts ps qs (_∙_ {A = emb-stype T} [Γ] [T]) [Z]) [T]
                (teleArgᵛ {i} {Z = Z′} Ts ps qs (_∙_ {A = emb-stype T} [Γ] [T]) [Z′])
                (reflᵛ {A = emb-stype T} [Γ] [T])
                (teleArgEqᵛ {i} {Z = Z} {Z′ = Z′} Ts ps qs (_∙_ {A = emb-stype T} [Γ] [T]) [Z] [Z′] [Z≡Z′])

  -- The branch type in normal form, as a telescope over the extension.
  module Branch {Γ lG Ss} ind j (ind∈ : ind ∈ₗ senv) (eqTs : SU.ctrArgsTypeList ind j PE.≡ just Ss)
                ([Γ] : ⊩ᵛ Γ) ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ]) where
    i = SU.SInd.name ind
    n = ctrArity Ss
    pos = all∈ (SU.ctrArgsTypesPositive ind j Ss eqTs)
    inds = ctrArgInds ind∈ eqTs
    [Δ] = extᵛ {i} Ss pos inds [Γ]
    [args] = PE.subst (λ ts → All₂ (ValidArg [Δ]) ts (map emb-stype Ss))
                      (map-cong (range n) (λ v → PE.cong var (PE.sym (plusZero ((n - 1) - v)))))
                      (ext-vars {i} Ss pos inds [Γ])
    [recs] = recArgsᵛ {i = i} [Δ] (λ v → var (((n - 1) - v) + 0)) (range n) Ss [args]
    e = ext-drop {i} Ss 0 pos inds [Γ] [Γ] (drop0 [Γ])

    Z : Term → Term
    Z Q = teleIhTy i j Ss Q lG 0 (ctrRecIndices i Ss)

    [Z] : ∀ {Q} → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Q ^ [ ! , ι lG ] / [Γ] ∙ [Ind]
        → ext Γ Ss ⊩ᵛ⟨ ∞ ⟩ Z Q ^ [ ! , ι lG ] / [Δ]
    [Z] {Q} [Q] = teleIhᵛ {P = Q} ind j Ss 0 (ctrRecIndices i Ss) ind∈ eqTs PE.refl
                          [Γ] [Ind] [Q] [Δ] e [args] [recs]

    [nf] : ∀ {Q} → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Q ^ [ ! , ι lG ] / [Γ] ∙ [Ind]
         → Γ ⊩ᵛ⟨ ∞ ⟩ foldr (Πarg ! lG) (Z Q) (map emb-stype Ss) ^ [ ! , ι lG ] / [Γ]
    [nf] {Q} [Q] = teleArgᵛ {i} {Z = Z Q} Ss pos inds [Γ] ([Z] [Q])

indRectBranchTyᵛ : ∀ {Γ P lG Ss} ind j
                 → ind ∈ₗ senv
                 → SU.ctrArgsTypeList ind j PE.≡ just Ss
                 → ([Γ] : ⊩ᵛ Γ)
                   ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
                 → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind]
                 → Γ ⊩ᵛ⟨ ∞ ⟩ indRectBranchTy (SU.SInd.name ind) j Ss P ! lG ^ [ ! , ι lG ] / [Γ]
indRectBranchTyᵛ {Γ} {P} {lG} {Ss} ind j ind∈ eqTs [Γ] [Ind] [P] =
  PE.subst (λ A → Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι lG ] / [Γ])
           (PE.sym (branchTy-nf (SU.SInd.name ind) j Ss P ! lG))
           (B.[nf] {P} [P])
  where module B = Branch {lG = lG} ind j ind∈ eqTs [Γ] [Ind]

indRectBranchTyCongᵛ : ∀ {Γ P P′ lG Ss} ind j
                     → ind ∈ₗ senv
                     → SU.ctrArgsTypeList ind j PE.≡ just Ss
                     → ([Γ] : ⊩ᵛ Γ)
                       ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
                       ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
                       ([P′] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
                     → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ≡ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind] / [P]
                     → ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ indRectBranchTy (SU.SInd.name ind) j Ss P ! lG ^ [ ! , ι lG ] / [Γ])
                     → Γ ⊩ᵛ⟨ ∞ ⟩ indRectBranchTy (SU.SInd.name ind) j Ss P ! lG
                               ≡ indRectBranchTy (SU.SInd.name ind) j Ss P′ ! lG ^ [ ! , ι lG ] / [Γ] / [A]
indRectBranchTyCongᵛ {Γ} {P} {P′} {lG} {Ss} ind j ind∈ eqTs [Γ] [Ind] [P] [P′] [P≡P′] [A] =
  let i = SU.SInd.name ind
      [nf] , [nf≡] =
        PE.subst₂ (λ A B → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι lG ] / [Γ])
                             → Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ B ^ [ ! , ι lG ] / [Γ] / [A])
                  (PE.sym (branchTy-nf i j Ss P ! lG)) (PE.sym (branchTy-nf i j Ss P′ ! lG))
                  (B.[nf] {P} [P]
                  , teleArgEqᵛ {i} {Z = B.Z P} {Z′ = B.Z P′} Ss B.pos B.inds [Γ] (B.[Z] {P} [P]) (B.[Z] {P′} [P′])
                      (teleIhEqᵛ {P = P} {P′} ind j Ss 0 (ctrRecIndices i Ss) ind∈ eqTs PE.refl
                                 [Γ] [Ind] [P] [P′] [P≡P′] B.[Δ] B.e B.[args] B.[recs] (B.[Z] {P} [P])))
  in  S.irrelevanceEq {A = indRectBranchTy i j Ss P ! lG} {B = indRectBranchTy i j Ss P′ ! lG}
                      [Γ] [Γ] [nf] [A] [nf≡]
  where module B = Branch {lG = lG} ind j ind∈ eqTs [Γ] [Ind]

private
  branchTyListConv : ∀ {Γ P P′ lG ms} ind (js : List (Nat × List SU.Type))
                   → ind ∈ₗ senv
                   → All (λ jTs → SU.ctrArgsTypeList ind (proj₁ jTs) PE.≡ just (proj₂ jTs)) js
                   → ([Γ] : ⊩ᵛ Γ)
                     ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
                     ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
                     ([P′] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
                   → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ≡ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind] / [P]
                   → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι lG ] / [Γ])
                                   → Γ ⊩ᵛ⟨ ∞ ⟩ m ∷ A ^ [ ! , ι lG ] / [Γ] / [A])
                          ms (map (λ jTs → indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P ! lG) js)
                   → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι lG ] / [Γ])
                                   → Γ ⊩ᵛ⟨ ∞ ⟩ m ∷ A ^ [ ! , ι lG ] / [Γ] / [A])
                          ms (map (λ jTs → indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P′ ! lG) js)
  branchTyListConv ind []ₗ ind∈ []ₐ [Γ] [Ind] [P] [P′] [P≡P′] []ₐ = []ₐ
  branchTyListConv {P = P} {P′} {lG} {m ∷ₗ ms} ind (jTs ∷ₗ js) ind∈ (eqTs ∷ₐ eqs) [Γ] [Ind] [P] [P′] [P≡P′]
                   (([A] , [m]) ∷ₐ [ms]) =
    let [A′] = indRectBranchTyᵛ {P = P′} {lG = lG} {Ss = proj₂ jTs} ind (proj₁ jTs) ind∈ eqTs [Γ] [Ind] [P′]
    in  ([A′] , convᵛ {t = m} {A = indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P ! lG}
                      {B = indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P′ ! lG} [Γ] [A] [A′]
                      (indRectBranchTyCongᵛ {P = P} {P′} {lG} {proj₂ jTs} ind (proj₁ jTs) ind∈ eqTs
                                            [Γ] [Ind] [P] [P′] [P≡P′] [A])
                      [m])
        ∷ₐ branchTyListConv {P = P} {P′} {lG} {ms} ind js ind∈ eqs [Γ] [Ind] [P] [P′] [P≡P′] [ms]

-- Valid methods for the motive P are valid methods for any motive P′ equal to P.
indRectBranchTyListConvᵛ : ∀ {Γ ind P P′ lG ms}
  → ind ∈ₗ senv
  → ([Γ] : ⊩ᵛ Γ)
    ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
    ([P] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
    ([P′] : Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind])
  → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ P ≡ P′ ^ [ ! , ι lG ] / [Γ] ∙ [Ind] / [P]
  → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι lG ] / [Γ])
                  → Γ ⊩ᵛ⟨ ∞ ⟩ m ∷ A ^ [ ! , ι lG ] / [Γ] / [A])
         ms (indRectBranchTyList ind P ! lG)
  → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι lG ] / [Γ])
                  → Γ ⊩ᵛ⟨ ∞ ⟩ m ∷ A ^ [ ! , ι lG ] / [Γ] / [A])
         ms (indRectBranchTyList ind P′ ! lG)
indRectBranchTyListConvᵛ {ind = ind} {P} {P′} {lG} {ms} ind∈ [Γ] [Ind] [P] [P′] [P≡P′] [ms] =
  branchTyListConv {P = P} {P′} {lG} {ms} ind
                   (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)) ind∈
                   (all∈ (zip-range-nth (SU.SInd.ctrArgsTypes ind))) [Γ] [Ind] [P] [P′] [P≡P′] [ms]
