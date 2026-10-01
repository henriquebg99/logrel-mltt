-- Validity of simple terms, and reducibility of the functions of the
-- equivalences of [equivs].
-- Simple terms are built from variables, lambdas, applications, constructors
-- and eliminators of inductive types only, so their validity does not depend
-- on the validity of cast (which itself needs the functions to be reducible).

import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Fundamental.SimpleTerm (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}

open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
import Definition.OUntyped senv as O
import Definition.OTyped senv as OT
import Definition.SUntyped as SU
import Definition.STyped senv as ST
import Definition.Equiv senv as Eq
open import Definition.Typed senv equivs
open import Definition.LogicalRelation senv swf equivs
import Definition.LogicalRelation.Irrelevance senv swf equivs as LR
open import Definition.LogicalRelation.Substitution senv swf equivs
import Definition.LogicalRelation.Substitution.Irrelevance senv swf equivs as S
open import Definition.LogicalRelation.Substitution.Escape senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Pi senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Lambda senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Application senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Ind senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.IndRect senv swf equivs
open import Definition.LogicalRelation.Fundamental.Variable senv swf equivs
open import Definition.LogicalRelation.EquivRed senv swf equivs

open import Tools.Product
open import Tools.Unit
open import Tools.List using (List; All; All₂; []ₐ; _∷ₐ_; _∈ₗ_; ∈ₗ-map)
import Tools.List as TL
import Tools.Nat as N
import Tools.PropositionalEquality as PE

------------------------------------------------------------------------
-- Embedding of simple contexts and terms

-- A simple context embedded on top of a context
infixl 30 _∙ˢ_
_∙ˢ_ : Con Term → ST.Con → Con Term
Γ ∙ˢ TL.[] = Γ
Γ ∙ˢ (A TL.∷ Δ) = (Γ ∙ˢ Δ) ∙ emb-stype A ^ [ ! , ι ⁰ ]

embˢ : SU.Term → Term
embˢ t = emb_oterm_term (O.emb-sterm-oterm t)

embAllˢ : List SU.Term → List Term
embAllˢ ts = emb-oterm-all (O.emb-sterm-oterm-all ts)

embVar : ∀ {Γ Δ x A} → x ST.∷ A ∈ Δ → x ∷ emb-stype A ^ [ ! , ι ⁰ ] ∈ Γ ∙ˢ Δ
embVar {Γ} {A TL.∷ Δ} ST.here =
  PE.subst (λ B → 0 ∷ B ^ [ ! , ι ⁰ ] ∈ Γ ∙ˢ Δ ∙ emb-stype A ^ [ ! , ι ⁰ ])
           (wk-emb-stype (step id) A) here
embVar {Γ} {B TL.∷ Δ} {A = A} (ST.there {x = x} h) =
  PE.subst (λ C → N.Nat.suc x ∷ C ^ [ ! , ι ⁰ ] ∈ Γ ∙ˢ Δ ∙ emb-stype B ^ [ ! , ι ⁰ ])
           (wk-emb-stype (step id) A) (there (embVar h))

-- The motive of an embedded eliminator is a weakened simple type
wk1-emb-stype : ∀ P → emb_oterm_term (O.wk1 (O.emb-stype-oterm P)) PE.≡ emb-stype P
wk1-emb-stype P =
  PE.trans (emb-wk1 (O.emb-stype-oterm P))
    (PE.trans (PE.cong wk1 (emb-stype-hom P)) (wk-emb-stype (step id) P))

embˢ-ctr : ∀ i j args → embˢ (SU.ctr i j args) PE.≡ ctr i j (embAllˢ args)
embˢ-ctr i j args =
  PE.trans (emb-ctr i j (O.emb-sterm-oterm-all args))
    (PE.cong (ctr i j) (PE.sym (emb-oterm-all-map (O.emb-sterm-oterm-all args))))

embˢ-IndRect : ∀ i P t ms → embˢ (SU.IndRect i P t ms) PE.≡ IndRect i ⁰ (emb-stype P) (embˢ t) (embAllˢ ms)
embˢ-IndRect i P t ms =
  PE.trans (emb-IndRect i ⁰ (O.wk1 (O.emb-stype-oterm P)) (O.emb-sterm-oterm t) (O.emb-sterm-oterm-all ms))
    (PE.cong (λ Q → IndRect i ⁰ Q (embˢ t) (embAllˢ ms)) (wk1-emb-stype P))

-- The embedded method types are the method types of the embedded motive
embˢ-branchTys : ∀ ind P → ind ∈ₗ senv →
  TL.map emb-stype (SU.indRectBranchTypeList ind P) PE.≡ indRectBranchTyList ind (emb-stype P) ! ⁰
embˢ-branchTys ind P ind∈ =
  PE.trans (PE.sym (PE.trans (map-map emb_oterm_term O.emb-stype-oterm Bs) (map-cong Bs emb-stype-hom)))
    (PE.trans (PE.cong (TL.map emb_oterm_term) (OT.emb-indRectBranchTyList-stype ind P ind∈))
      (PE.trans (emb-indRectBranchTyList ind (O.wk1 (O.emb-stype-oterm P)) ! ⁰)
        (PE.cong (λ Q → indRectBranchTyList ind Q ! ⁰) (wk1-emb-stype P))))
  where
  Bs = SU.indRectBranchTypeList ind P

-- Embedded simple terms only depend on the variables of their context
private
  subst-emb-stype-oterm : ∀ A σ → subst σ (emb_oterm_term (O.emb-stype-oterm A)) PE.≡ emb_oterm_term (O.emb-stype-oterm A)
  subst-emb-stype-oterm A σ =
    PE.trans (PE.cong (subst σ) (emb-stype-hom A))
      (PE.trans (subst-emb-stype σ A) (PE.sym (emb-stype-hom A)))

  subst-wk1-emb-stype : ∀ P σ → subst σ (emb_oterm_term (O.wk1 (O.emb-stype-oterm P)))
                                  PE.≡ emb_oterm_term (O.wk1 (O.emb-stype-oterm P))
  subst-wk1-emb-stype P σ =
    PE.trans (PE.cong (subst σ) (wk1-emb-stype P))
      (PE.trans (subst-emb-stype σ P) (PE.sym (wk1-emb-stype P)))

mutual
  subst-embˢ-fix : ∀ {Δ t A σ}
    → (∀ {x B} → x ST.∷ B ∈ Δ → σ x PE.≡ var x)
    → Δ ST.⊢ t ∷ A → subst σ (embˢ t) PE.≡ embˢ t
  subst-embˢ-fix fix (ST.varⱼ h) = fix h
  subst-embˢ-fix fix (ST.appⱼ ⊢f ⊢a) =
    PE.cong₂ (λ f a → f ∘ a ^ ⁰) (subst-embˢ-fix fix ⊢f) (subst-embˢ-fix fix ⊢a)
  subst-embˢ-fix {σ = σ} fix (ST.lamⱼ {A = A} _ ⊢t) =
    PE.cong₂ (λ A t → lam A ▹ t ^ ⁰) (subst-emb-stype-oterm A σ) (subst-embˢ-fix fix′ ⊢t)
    where
    fix′ : ∀ {x B} → x ST.∷ B ∈ (A ST.∙ _) → liftSubst σ x PE.≡ var x
    fix′ ST.here = PE.refl
    fix′ (ST.there h) = PE.cong wk1 (fix h)
  subst-embˢ-fix fix (ST.ctrⱼ _ _ _ ⊢args) =
    PE.cong (gen _) (subst-embGenˢ-fix fix ⊢args)
  subst-embˢ-fix {σ = σ} fix (ST.indRectⱼ {ind = ind} {P = P} _ _ ⊢t ⊢ms) =
    PE.cong₂ (λ P′ rest → gen (IndRectkind (SU.SInd.name ind) ⁰) (⟦ 1 , P′ ⟧ TL.∷ rest))
      (subst-wk1-emb-stype P (liftSubst σ))
      (PE.cong₂ (λ t ms → ⟦ 0 , t ⟧ TL.∷ ms) (subst-embˢ-fix fix ⊢t) (subst-embGenˢ-fix fix ⊢ms))

  subst-embGenˢ-fix : ∀ {Δ ts As σ}
    → (∀ {x B} → x ST.∷ B ∈ Δ → σ x PE.≡ var x)
    → Δ ST.⊢All ts ∷ As
    → substGen σ (emb_otermGen (TL.map (λ t → ⟦ 0 , t ⟧) (O.emb-sterm-oterm-all ts)))
      PE.≡ emb_otermGen (TL.map (λ t → ⟦ 0 , t ⟧) (O.emb-sterm-oterm-all ts))
  subst-embGenˢ-fix fix ST.εⱼ = PE.refl
  subst-embGenˢ-fix fix (ST.consⱼ ⊢t ⊢ts) =
    PE.cong₂ TL._∷_ (PE.cong (λ t → ⟦ 0 , t ⟧) (subst-embˢ-fix fix ⊢t))
      (subst-embGenˢ-fix fix ⊢ts)

-- Closed simple terms embed to closed terms
subst-embˢ-closed : ∀ {t A} → TL.[] ST.⊢ t ∷ A → ∀ σ → subst σ (embˢ t) PE.≡ embˢ t
subst-embˢ-closed ⊢t σ = subst-embˢ-fix (λ ()) ⊢t

------------------------------------------------------------------------
-- Validity of simple types and contexts

emb-stypeᵛ : ∀ {Γ} A → SU.indsInSEnv senv A → ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ∞ ⟩ emb-stype A ^ [ ! , ι ⁰ ] / [Γ]
emb-stypeᵛ (SU.Ind i) i∈ [Γ] = Indᵛ i∈ [Γ]
emb-stypeᵛ (SU.Arrow A B) (A∈ , B∈) [Γ] =
  let [A] = emb-stypeᵛ A A∈ [Γ]
  in  Πᵛ {emb-stype A} {emb-stype B} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A]
         (emb-stypeᵛ B B∈ (_∙_ {A = emb-stype A} [Γ] [A]))

validˢ : ∀ {Γ} Δ → ⊩ᵛ Γ → All (SU.indsInSEnv senv) Δ → ⊩ᵛ Γ ∙ˢ Δ
validˢ TL.[] [Γ] []ₐ = [Γ]
validˢ (A TL.∷ Δ) [Γ] (A∈ ∷ₐ Δ∈) =
  let [ΓΔ] = validˢ Δ [Γ] Δ∈
  in  _∙_ {A = emb-stype A} [ΓΔ] (emb-stypeᵛ A A∈ [ΓΔ])

escapeAllᵛ : ∀ {Γ ts As} ([Γ] : ⊩ᵛ Γ)
  → All₂ (λ t A → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                  → Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A]) ts As
  → Γ ⊢All ts ∷ As ^ [ ! , ι ⁰ ]
escapeAllᵛ [Γ] []ₐ = εⱼ
escapeAllᵛ [Γ] (([A] , [t]) ∷ₐ ps) = consⱼ (escapeTermᵛ [Γ] [A] [t]) (escapeAllᵛ [Γ] ps)

------------------------------------------------------------------------
-- Fundamental theorem for simple terms

mutual
  simpleᵛ : ∀ {Γ Δ t A} ([Γ] : ⊩ᵛ Γ) (Δ∈ : All (SU.indsInSEnv senv) Δ)
          → Δ ST.⊢ t ∷ A
          → ∃ λ ([A] : Γ ∙ˢ Δ ⊩ᵛ⟨ ∞ ⟩ emb-stype A ^ [ ! , ι ⁰ ] / validˢ Δ [Γ] Δ∈)
          → Γ ∙ˢ Δ ⊩ᵛ⟨ ∞ ⟩ embˢ t ∷ emb-stype A ^ [ ! , ι ⁰ ] / validˢ Δ [Γ] Δ∈ / [A]
  simpleᵛ {Δ = Δ} [Γ] Δ∈ (ST.varⱼ h) = fundamentalVar (embVar h) (validˢ Δ [Γ] Δ∈)
  simpleᵛ {Δ = Δ} [Γ] Δ∈ (ST.appⱼ {f} {a} {A} {B} ⊢f ⊢a) =
    let [ΓΔ] = validˢ Δ [Γ] Δ∈
        _ , B∈ = OT.st-type-inds Δ∈ ⊢f
        [ΠAB] , [f] = simpleᵛ [Γ] Δ∈ ⊢f
        [A] , [a] = simpleᵛ [Γ] Δ∈ ⊢a
        [B] = emb-stypeᵛ B B∈ (_∙_ {A = emb-stype A} [ΓΔ] [A])
        [B]′ = emb-stypeᵛ B B∈ [ΓΔ]
        [f∘a] = appᵛ {F = emb-stype A} {G = emb-stype B} {rF = !} {lF = ⁰} {lG = ⁰} {lΠ = ⁰} {t = embˢ f} {u = embˢ a}
                     [ΓΔ] [A] [B] [ΠAB] [f] [a]
    in  [B]′
    ,   S.irrelevanceTerm′ {A = emb-stype B [ embˢ a ]} {A′ = emb-stype B} {t = embˢ f ∘ embˢ a ^ ⁰}
          (subst-emb-stype (sgSubst (embˢ a)) B) PE.refl [ΓΔ] [ΓΔ]
          (substSΠ {emb-stype A} {emb-stype B} {embˢ a} [ΓΔ] [A] [ΠAB] [a]) [B]′ [f∘a]
  simpleᵛ {Δ = Δ} [Γ] Δ∈ (ST.lamⱼ {A} {B} {t} A∈ ⊢t) =
    let [ΓΔ] = validˢ Δ [Γ] Δ∈
        [A] = emb-stypeᵛ A A∈ [ΓΔ]
        [B] , [t] = simpleᵛ [Γ] (A∈ ∷ₐ Δ∈) ⊢t
        [ΠAB] = Πᵛ {emb-stype A} {emb-stype B} (≡is≤ PE.refl) (≡is≤ PE.refl) [ΓΔ] [A] [B]
    in  [ΠAB]
    ,   S.irrelevanceTerm′′ {A = Π emb-stype A ^ ! ° ⁰ ▹ emb-stype B ° ⁰ ° ⁰ ^ !}
          {t = lam emb-stype A ▹ embˢ t ^ ⁰} {t′ = embˢ (SU.lam A t)}
          PE.refl (PE.cong (λ F → lam F ▹ embˢ t ^ ⁰) (PE.sym (emb-stype-hom A))) PE.refl
          [ΓΔ] [ΓΔ] [ΠAB] [ΠAB]
          (lamᵛ {F = emb-stype A} {G = emb-stype B} {rF = !} {lF = ⁰} {lG = ⁰} {lΠ = ⁰} {t = embˢ t}
                (≡is≤ PE.refl) (≡is≤ PE.refl) [ΓΔ] [A] [B] [t])
  simpleᵛ {Δ = Δ} [Γ] Δ∈ (ST.ctrⱼ {ind} {j} {args} {Ts} ind∈ eq _ ⊢args) =
    let [ΓΔ] = validˢ Δ [Γ] Δ∈
        i = SU.SInd.name ind
        [Ind] = Indᵛ {i = i} {l = ∞} (∈ₗ-map SU.SInd.name ind∈) [ΓΔ]
        [args] = simpleAllᵛ [Γ] Δ∈ ⊢args
    in  [Ind]
    ,   S.irrelevanceTerm′′ {A = Ind i} {t = ctr i j (embAllˢ args)} {t′ = embˢ (SU.ctr i j args)}
          PE.refl (PE.sym (embˢ-ctr i j args)) PE.refl [ΓΔ] [ΓΔ] [Ind] [Ind]
          (ctrᵛ {ind = ind} {j = j} {args = embAllˢ args} {Ts = Ts} {l = ∞}
                [ΓΔ] [Ind] ind∈ eq (escapeAllᵛ [ΓΔ] [args]) [args])
  simpleᵛ {Γ} {Δ} [Γ] Δ∈ (ST.indRectⱼ {ind} {P} {t} {ms} ind∈ P∈ ⊢t ⊢ms) =
    let [ΓΔ] = validˢ Δ [Γ] Δ∈
        i = SU.SInd.name ind
        [Ind] = Indᵛ {i = i} {l = ∞} (∈ₗ-map SU.SInd.name ind∈) [ΓΔ]
        [P] = emb-stypeᵛ P P∈ (_∙_ {A = Ind i} [ΓΔ] [Ind])
        [P]′ = emb-stypeᵛ P P∈ [ΓΔ]
        [Indt] , [t] = simpleᵛ [Γ] Δ∈ ⊢t
        [t]′ = S.irrelevanceTerm {A = Ind i} {t = embˢ t} [ΓΔ] [ΓΔ] [Indt] [Ind] [t]
        [Pt] = S.irrelevance′ {A = emb-stype P} {A′ = emb-stype P [ embˢ t ]}
                 (PE.sym (subst-emb-stype (sgSubst (embˢ t)) P)) [ΓΔ] [ΓΔ] [P]′
        [ms] = PE.subst (λ Bs → All₂ (λ m B → ∃ λ ([B] : Γ ∙ˢ Δ ⊩ᵛ⟨ ∞ ⟩ B ^ [ ! , ι ⁰ ] / [ΓΔ])
                                             → Γ ∙ˢ Δ ⊩ᵛ⟨ ∞ ⟩ m ∷ B ^ [ ! , ι ⁰ ] / [ΓΔ] / [B])
                                      (embAllˢ ms) Bs)
                        (embˢ-branchTys ind P ind∈) (simpleAllᵛ [Γ] Δ∈ ⊢ms)
        [rec] = IndRectᵛ {ind = ind} {P = emb-stype P} {rG = !} {lG = ⁰} {t = embˢ t}
                         {ms = embAllˢ ms} {l = ∞}
                         (λ _ → PE.refl) [ΓΔ] ind∈ [Ind] [P] [t]′ [Pt] (escapeAllᵛ [ΓΔ] [ms]) [ms]
    in  [P]′
    ,   S.irrelevanceTerm′′ {A = emb-stype P [ embˢ t ]} {A′ = emb-stype P}
          {t = IndRect i ⁰ (emb-stype P) (embˢ t) (embAllˢ ms)} {t′ = embˢ (SU.IndRect i P t ms)}
          (subst-emb-stype (sgSubst (embˢ t)) P) (PE.sym (embˢ-IndRect i P t ms)) PE.refl
          [ΓΔ] [ΓΔ] [Pt] [P]′ [rec]

  simpleAllᵛ : ∀ {Γ Δ ts As} ([Γ] : ⊩ᵛ Γ) (Δ∈ : All (SU.indsInSEnv senv) Δ)
             → Δ ST.⊢All ts ∷ As
             → All₂ (λ t A → ∃ λ ([A] : Γ ∙ˢ Δ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι ⁰ ] / validˢ Δ [Γ] Δ∈)
                             → Γ ∙ˢ Δ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / validˢ Δ [Γ] Δ∈ / [A])
                    (embAllˢ ts) (TL.map emb-stype As)
  simpleAllᵛ [Γ] Δ∈ ST.εⱼ = []ₐ
  simpleAllᵛ [Γ] Δ∈ (ST.consⱼ ⊢t ⊢ts) = simpleᵛ [Γ] Δ∈ ⊢t ∷ₐ simpleAllᵛ [Γ] Δ∈ ⊢ts

------------------------------------------------------------------------
-- Reducibility of the functions of the equivalences

-- Closed simple functions between inductive types are reducible
closedFunRed : ∀ {Γ i j s} (⊢Γ : ⊢ Γ) (i∈ : i ∈ₗ SU.indNames senv) (j∈ : j ∈ₗ SU.indNames senv)
             → TL.[] ST.⊢ s ∷ SU.Arrow (SU.Ind i) (SU.Ind j)
             → Γ ⊩⟨ ι ⁰ ⟩ embˢ s ∷ Π Ind i ^ ! ° ⁰ ▹ Ind j ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] / ΠIndInd i j i∈ j∈ ⊢Γ
closedFunRed {s = s} ⊢Γ i∈ j∈ ⊢s =
  let [A] , [s] = simpleᵛ {Γ = ε} ε []ₐ ⊢s
  in  LR.irrelevanceTerm″ PE.refl PE.refl PE.refl (subst-id (embˢ s))
                          (proj₁ ([A] {σ = idSubst} ⊢Γ tt)) (ΠIndInd _ _ i∈ j∈ ⊢Γ)
                          (proj₁ ([s] {σ = idSubst} ⊢Γ tt))

-- The forward function of the equivalence between two inductives with the
-- same representative
⊢repr-fwd : ∀ {C i j} (i∈ : i ∈ₗ SU.indNames senv) (j∈ : j ∈ₗ SU.indNames senv) (H : reprInd i PE.≡ reprInd j)
          → C ST.⊢ Eq.Equiv.fwd (Eq.repr-equiv equivs i j i∈ j∈ H) ∷ SU.Arrow (SU.Ind i) (SU.Ind j)
⊢repr-fwd {C} {i} {j} i∈ j∈ H =
  PE.subst₂ (λ a b → C ST.⊢ Eq.Equiv.fwd e ∷ SU.Arrow (SU.Ind a) (SU.Ind b))
            (Eq.repr-equiv-indA equivs i j i∈ j∈ H)
            (Eq.repr-equiv-indB equivs i j i∈ j∈ H)
            (Eq.Equiv.⊢fwd e)
  where
  e = Eq.repr-equiv equivs i j i∈ j∈ H

-- Validity of the application of the forward function of such an equivalence
repr-fwd-appᵛ : ∀ {Γ i j t} (i∈ : i ∈ₗ SU.indNames senv) (j∈ : j ∈ₗ SU.indNames senv) (H : reprInd i PE.≡ reprInd j)
                ([Γ] : ⊩ᵛ Γ)
                ([Indi] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ])
                ([Indj] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind j ^ [ ! , ι ⁰ ] / [Γ])
              → Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ Ind i ^ [ ! , ι ⁰ ] / [Γ] / [Indi]
              → Γ ⊩ᵛ⟨ ∞ ⟩ emb_oterm_term (Eq.fwdₒ (Eq.repr-equiv equivs i j i∈ j∈ H)) ∘ t ^ ⁰
                  ∷ Ind j ^ [ ! , ι ⁰ ] / [Γ] / [Indj]
repr-fwd-appᵛ {Γ} {i} {j} {t} i∈ j∈ H [Γ] [Indi] [Indj] [t] =
  let f = embˢ (Eq.Equiv.fwd (Eq.repr-equiv equivs i j i∈ j∈ H))
      [Π] , [f] = simpleᵛ {Γ = Γ} [Γ] []ₐ (⊢repr-fwd {TL.[]} i∈ j∈ H)
      [Indi]′ = Indᵛ {l = ∞} i∈ [Γ]
      [t]′ = S.irrelevanceTerm {A = Ind i} {t = t} [Γ] [Γ] [Indi] [Indi]′ [t]
  in  S.irrelevanceTerm {A = Ind j} {t = f ∘ t ^ ⁰} [Γ] [Γ]
        (substSΠ {Ind i} {Ind j} {t} [Γ] [Indi]′ [Π] [t]′) [Indj]
        (appᵛ {F = Ind i} {G = Ind j} {rF = !} {lF = ⁰} {lG = ⁰} {lΠ = ⁰} {t = f} {u = t}
              [Γ] [Indi]′ (λ {Δ} {σ} → Indᵛ {l = ∞} j∈ (_∙_ {A = Ind i} [Γ] [Indi]′) {Δ} {σ}) [Π] [f] [t]′)

equivRed : EquivRed
equivRed = record
  { [fwd] = λ {Γ} {e} ⊢Γ _ →
      closedFunRed ⊢Γ (Eq.Equiv.indA∈ e) (Eq.Equiv.indB∈ e) (Eq.Equiv.⊢fwd e)
  ; [bwd] = λ {Γ} {e} ⊢Γ _ →
      closedFunRed ⊢Γ (Eq.Equiv.indB∈ e) (Eq.Equiv.indA∈ e) (Eq.Equiv.⊢bwd e)
  ; [repr-fwd] = λ ⊢Γ i∈ j∈ H → closedFunRed ⊢Γ i∈ j∈ (⊢repr-fwd i∈ j∈ H)
  }
