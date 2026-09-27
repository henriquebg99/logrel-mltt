import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.Ind (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}

open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.LogicalRelation senv swf equivs
open import Definition.LogicalRelation.Irrelevance senv swf equivs
open import Definition.LogicalRelation.ShapeView senv swf equivs
open import Definition.LogicalRelation.Properties senv swf equivs
open import Definition.LogicalRelation.Substitution senv swf equivs
open import Definition.LogicalRelation.Substitution.Introductions.Universe senv swf equivs
open import Tools.Nat
open import Tools.Product
open import Tools.Maybe using (just)
open import Tools.List using (All; All₂; All₃; []ₐ; _∷ₐ_; _∈ₗ_; ∈ₗ-map; map; length; length-map; all∈)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU

------------------------------------------------------------------------
-- Constructor arguments.
-- Positivity forces every constructor argument type to be some Ind k, so a
-- reducible argument is a reducible term of its own inductive type.

-- Congruence helper for the arguments of a constructor
≅AllInd : ∀ {Γ args args' Ts}
        → ⊢ Γ
        → All (SU.indsInSEnv senv) Ts
        → All₃ (λ a a' A → ∃ λ k → A PE.≡ Ind k × Γ ⊩Ind a ≡ a' ∷Ind k) args args' (map emb-stype Ts)
        → All₃ (λ a a' A → Γ ⊢ a ≅ a' ∷ A ^ [ ! , ι ⁰ ]) args args' (map emb-stype Ts)
≅AllInd {Ts = []ₗ} ⊢Γ []ₐ []ₐ = []ₐ
≅AllInd {Ts = SU.Ind _ ∷ₗ Ts} ⊢Γ (k∈ ∷ₐ ks) ((k , PE.refl , Indₜ₌ n n′ d d′ n≡n′ prop) ∷ₐ ps) =
  let indN , indN′ = splitInd prop
  in  ≅ₜ-red (id (univ (Indⱼ′ ⊢Γ k∈))) (redₜ d) (redₜ d′) Indₙ
             (inductiveWhnf indN) (inductiveWhnf indN′) n≡n′
      ∷ₐ ≅AllInd ⊢Γ ks ps
≅AllInd {Ts = SU.Arrow _ _ ∷ₗ Ts} ⊢Γ (_ ∷ₐ _) ((_ , () , _) ∷ₐ _)

-- Reducible arguments, at their own (reducible) types
indArgs : ∀ {l Γ args Ts}
        → All (λ T → ∃ λ i → SU.isPositive i T) Ts
        → All₂ (λ a A → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ])
                          → Γ ⊩⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [A]) args (map emb-stype Ts)
        → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Γ ⊩Ind a ∷Ind k) args (map emb-stype Ts)
indArgs {Ts = []ₗ} []ₐ []ₐ = []ₐ
indArgs {l} {Ts = SU.Ind k ∷ₗ Ts} (_ ∷ₐ pos) (([A] , [a]) ∷ₐ ps) =
  (k , PE.refl , irrelevanceTerm {l′ = l} [A] (Indᵣ (idRed:*: (escape [A]))) [a]) ∷ₐ indArgs pos ps
indArgs {Ts = SU.Arrow _ _ ∷ₗ Ts} ((_ , ()) ∷ₐ _) _

indArgsEq : ∀ {l Γ args args' Ts}
          → All (λ T → ∃ λ i → SU.isPositive i T) Ts
          → All₃ (λ a a' A → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ])
                               → Γ ⊩⟨ l ⟩ a ≡ a' ∷ A ^ [ ! , ι ⁰ ] / [A])
                 args args' (map emb-stype Ts)
          → All₃ (λ a a' A → ∃ λ k → A PE.≡ Ind k × Γ ⊩Ind a ≡ a' ∷Ind k) args args' (map emb-stype Ts)
indArgsEq {Ts = []ₗ} []ₐ []ₐ = []ₐ
indArgsEq {l} {Ts = SU.Ind k ∷ₗ Ts} (_ ∷ₐ pos) (([A] , [a≡a′]) ∷ₐ ps) =
  (k , PE.refl , irrelevanceEqTerm {l′ = l} [A] (Indᵣ (idRed:*: (escape [A]))) [a≡a′])
  ∷ₐ indArgsEq pos ps
indArgsEq {Ts = SU.Arrow _ _ ∷ₗ Ts} ((_ , ()) ∷ₐ _) _

-- Constructor argument types are positive
ctrArgsPos : ∀ {ind j Ts} → SU.ctrArgsTypeList ind j PE.≡ just Ts
           → All (λ T → ∃ λ i → SU.isPositive i T) Ts
ctrArgsPos {ind} {j} {Ts} eq =
  all∈ (λ T T∈ → SU.SInd.name ind , SU.ctrArgsTypesPositive ind j Ts eq T T∈)

private
  ⊢All-length : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → length ts PE.≡ length As
  ⊢All-length εⱼ = PE.refl
  ⊢All-length (consⱼ _ rest) = PE.cong 1+ (⊢All-length rest)

------------------------------------------------------------------------
-- Reducible constructors (specific Ind derivation)

ctrTerm′ : ∀ {l Γ ind j args Ts}
         → ([Ind] : Γ ⊩⟨ l ⟩Ind Ind (SU.SInd.name ind) ^ SU.SInd.name ind)
         → ind ∈ₗ senv
         → SU.ctrArgsTypeList ind j PE.≡ just Ts
         → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
         → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Γ ⊩Ind a ∷Ind k) args (map emb-stype Ts)
         → Γ ⊩⟨ l ⟩ ctr (SU.SInd.name ind) j args ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / Ind-intr [Ind]
ctrTerm′ {l} {ind = ind} {j = j} {args = args} {Ts = Ts} (noemb D) ind∈ eq ⊢args ps =
  let ⊢Γ = wf (escape {l = l} (Ind-intr (noemb D)))
      ⊢ctr = Ctrⱼ ⊢Γ ind∈ eq ⊢args
  in  Indₜ (ctr (SU.SInd.name ind) j args) (idRedTerm:*: ⊢ctr)
           (≅-ctr-cong ⊢Γ ind∈ eq (≅AllInd ⊢Γ (ctrArgInds ind∈ eq) (reflAllInd ps)))
           (ctrᵣ ind∈ PE.refl eq ps)
ctrTerm′ (emb emb< x) ind∈ eq ⊢args ps = ctrTerm′ x ind∈ eq ⊢args ps
ctrTerm′ (emb ∞< x) ind∈ eq ⊢args ps = ctrTerm′ x ind∈ eq ⊢args ps

-- Reducible inductive constructors from reducible arguments.
ctrTerm : ∀ {l Γ ind j args Ts}
        → ([Ind] : Γ ⊩⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ])
        → ind ∈ₗ senv
        → SU.ctrArgsTypeList ind j PE.≡ just Ts
        → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
        → All₂ (λ a A → ∃ λ k → A PE.≡ Ind k × Γ ⊩Ind a ∷Ind k) args (map emb-stype Ts)
        → Γ ⊩⟨ l ⟩ ctr (SU.SInd.name ind) j args ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Ind]
ctrTerm [Ind] ind∈ eq ⊢args ps =
  irrelevanceTerm (Ind-intr (Ind-elim [Ind])) [Ind]
                  (ctrTerm′ (Ind-elim [Ind]) ind∈ eq ⊢args ps)

------------------------------------------------------------------------
-- Reducible constructor equality

ctrEqTerm′ : ∀ {l Γ ind j args args' Ts}
           → ([Ind] : Γ ⊩⟨ l ⟩Ind Ind (SU.SInd.name ind) ^ SU.SInd.name ind)
           → ind ∈ₗ senv
           → SU.ctrArgsTypeList ind j PE.≡ just Ts
           → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
           → Γ ⊢All args' ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
           → All₃ (λ a a' A → ∃ λ k → A PE.≡ Ind k × Γ ⊩Ind a ≡ a' ∷Ind k) args args' (map emb-stype Ts)
           → Γ ⊩⟨ l ⟩ ctr (SU.SInd.name ind) j args ≡ ctr (SU.SInd.name ind) j args'
                 ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / Ind-intr [Ind]
ctrEqTerm′ {l} {ind = ind} {j = j} {args = args} {args' = args'} {Ts = Ts} (noemb D) ind∈ eq ⊢args ⊢args' ps =
  let ⊢Γ = wf (escape {l = l} (Ind-intr (noemb D)))
      ⊢ctr  = Ctrⱼ ⊢Γ ind∈ eq ⊢args
      ⊢ctr' = Ctrⱼ ⊢Γ ind∈ eq ⊢args'
  in  Indₜ₌ (ctr (SU.SInd.name ind) j args) (ctr (SU.SInd.name ind) j args')
            (idRedTerm:*: ⊢ctr) (idRedTerm:*: ⊢ctr')
            (≅-ctr-cong ⊢Γ ind∈ eq (≅AllInd ⊢Γ (ctrArgInds ind∈ eq) ps))
            (ctrᵣ ind∈ PE.refl eq ps)
ctrEqTerm′ (emb emb< x) ind∈ eq ⊢args ⊢args' ps = ctrEqTerm′ x ind∈ eq ⊢args ⊢args' ps
ctrEqTerm′ (emb ∞< x) ind∈ eq ⊢args ⊢args' ps = ctrEqTerm′ x ind∈ eq ⊢args ⊢args' ps

ctrEqTerm : ∀ {l Γ ind j args args' Ts}
          → ([Ind] : Γ ⊩⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ])
          → ind ∈ₗ senv
          → SU.ctrArgsTypeList ind j PE.≡ just Ts
          → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
          → Γ ⊢All args' ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
          → All₃ (λ a a' A → ∃ λ k → A PE.≡ Ind k × Γ ⊩Ind a ≡ a' ∷Ind k) args args' (map emb-stype Ts)
          → Γ ⊩⟨ l ⟩ ctr (SU.SInd.name ind) j args ≡ ctr (SU.SInd.name ind) j args'
                ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Ind]
ctrEqTerm [Ind] ind∈ eq ⊢args ⊢args' ps =
  irrelevanceEqTerm (Ind-intr (Ind-elim [Ind])) [Ind]
                    (ctrEqTerm′ (Ind-elim [Ind]) ind∈ eq ⊢args ⊢args' ps)

------------------------------------------------------------------------
-- Validity of Ind i

Indᵛ : ∀ {Γ i l} → i ∈ₗ SU.indNames senv → ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Ind i ^ [ ! , ι ⁰ ] / [Γ]
Indᵛ {i = i} i∈ [Γ] ⊢Δ [σ] =
  Indᵣ (idRed:*: (univ (Indⱼ′ ⊢Δ i∈))) , λ _ _ → id (univ (Indⱼ′ ⊢Δ i∈))

-- Validity of Ind i as a term of U ⁰.
Indᵗᵛ : ∀ {Γ i} → i ∈ₗ SU.indNames senv → ([Γ] : ⊩ᵛ Γ)
     → Γ ⊩ᵛ⟨ ι ¹ ⟩ Ind i ∷ Univ ! ⁰ ^ [ ! , ι ¹ ] / [Γ] / Uᵛ emb< [Γ]
Indᵗᵛ {i = i} i∈ [Γ] ⊢Δ [σ] =
  let UIndₜ = Uₜ (Ind i) (idRedTerm:*: (Indⱼ′ ⊢Δ i∈)) Indₙ (≅ₜ-Indrefl ⊢Δ i∈)
                 (λ _ ⊢Δ₁ → Indᵣ (idRed:*: (univ (Indⱼ′ ⊢Δ₁ i∈))))
  in  UIndₜ , λ _ _ → Uₜ₌ UIndₜ UIndₜ (≅ₜ-Indrefl ⊢Δ i∈)
                            λ _ ⊢Δ₂ → id (univ (Indⱼ′ ⊢Δ₂ i∈))

------------------------------------------------------------------------
-- Apply validity All under a concrete substitution.
-- Constructor argument types are closed, so they are left untouched.

applyAllᵛ : ∀ {Γ Δ σ l args Ts}
          → ([Γ] : ⊩ᵛ Γ)
          → (⊢Δ : ⊢ Δ)
          → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → All₂ (λ a A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                            → Γ ⊩ᵛ⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A]) args (map emb-stype Ts)
          → All₂ (λ a A → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ])
                            → Δ ⊩⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [A])
                 (map (subst σ) args) (map emb-stype Ts)
applyAllᵛ {Ts = []ₗ} [Γ] ⊢Δ [σ] []ₐ = []ₐ
applyAllᵛ {Δ = Δ} {σ = σ} {l = l} {Ts = T ∷ₗ Ts} [Γ] ⊢Δ [σ] (([A] , [a]) ∷ₐ [as]) =
  PE.subst (λ B → ∃ λ ([B] : Δ ⊩⟨ l ⟩ B ^ [ ! , ι ⁰ ]) → Δ ⊩⟨ l ⟩ _ ∷ B ^ [ ! , ι ⁰ ] / [B])
           (subst-emb-stype σ T)
           (proj₁ ([A] ⊢Δ [σ]) , proj₁ ([a] ⊢Δ [σ]))
  ∷ₐ applyAllᵛ [Γ] ⊢Δ [σ] [as]

applyAllEqᵛ : ∀ {Γ Δ σ σ′ l args Ts}
            → ([Γ] : ⊩ᵛ Γ)
            → (⊢Δ : ⊢ Δ)
            → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
            → ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
            → ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
            → All₂ (λ a A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                              → Γ ⊩ᵛ⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A]) args (map emb-stype Ts)
            → All₃ (λ a a' A → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ])
                                 → Δ ⊩⟨ l ⟩ a ≡ a' ∷ A ^ [ ! , ι ⁰ ] / [A])
                   (map (subst σ) args) (map (subst σ′) args) (map emb-stype Ts)
applyAllEqᵛ {Ts = []ₗ} [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] []ₐ = []ₐ
applyAllEqᵛ {Δ = Δ} {σ = σ} {l = l} {Ts = T ∷ₗ Ts} [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] (([A] , [a]) ∷ₐ [as]) =
  PE.subst (λ B → ∃ λ ([B] : Δ ⊩⟨ l ⟩ B ^ [ ! , ι ⁰ ]) → Δ ⊩⟨ l ⟩ _ ≡ _ ∷ B ^ [ ! , ι ⁰ ] / [B])
           (subst-emb-stype σ T)
           (proj₁ ([A] ⊢Δ [σ]) , proj₂ ([a] ⊢Δ [σ]) [σ′] [σ≡σ′])
  ∷ₐ applyAllEqᵛ [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [as]

applyAll₂ᵛ : ∀ {Γ Δ σ l args args' Ts}
           → ([Γ] : ⊩ᵛ Γ)
           → (⊢Δ : ⊢ Δ)
           → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           → All₃ (λ a a' A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                                → Γ ⊩ᵛ⟨ l ⟩ a ≡ a' ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A])
                  args args' (map emb-stype Ts)
           → All₃ (λ a a' A → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ])
                                → Δ ⊩⟨ l ⟩ a ≡ a' ∷ A ^ [ ! , ι ⁰ ] / [A])
                  (map (subst σ) args) (map (subst σ) args') (map emb-stype Ts)
applyAll₂ᵛ {Ts = []ₗ} [Γ] ⊢Δ [σ] []ₐ = []ₐ
applyAll₂ᵛ {Δ = Δ} {σ = σ} {l = l} {Ts = T ∷ₗ Ts} [Γ] ⊢Δ [σ] (([A] , [a≡a']) ∷ₐ ps) =
  PE.subst (λ B → ∃ λ ([B] : Δ ⊩⟨ l ⟩ B ^ [ ! , ι ⁰ ]) → Δ ⊩⟨ l ⟩ _ ≡ _ ∷ B ^ [ ! , ι ⁰ ] / [B])
           (subst-emb-stype σ T)
           (proj₁ ([A] ⊢Δ [σ]) , [a≡a'] ⊢Δ [σ])
  ∷ₐ applyAll₂ᵛ [Γ] ⊢Δ [σ] ps

-- Escape of reducible arguments
escapeArgs : ∀ {Δ l args As}
           → All₂ (λ a A → ∃ λ ([A] : Δ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ])
                             → Δ ⊩⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [A]) args As
           → Δ ⊢All args ∷ As ^ [ ! , ι ⁰ ]
escapeArgs []ₐ = εⱼ
escapeArgs (([A] , [a]) ∷ₐ ps) = consⱼ (escapeTerm [A] [a]) (escapeArgs ps)

------------------------------------------------------------------------
-- Validity of constructors

ctrᵛ : ∀ {Γ ind j args Ts l}
     → ([Γ] : ⊩ᵛ Γ)
     → ([Ind] : Γ ⊩ᵛ⟨ l ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
     → (ind∈ : ind ∈ₗ senv)
     → (eq : SU.ctrArgsTypeList ind j PE.≡ just Ts)
     → (⊢args : Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ])
     → All₂ (λ a A → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
                       → Γ ⊩ᵛ⟨ l ⟩ a ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A]) args (map emb-stype Ts)
     → Γ ⊩ᵛ⟨ l ⟩ ctr (SU.SInd.name ind) j args ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind]
ctrᵛ {ind = ind} {j = j} {args = args} {Ts = Ts} {l = l} [Γ] [Ind] ind∈ eq ⊢args [args] {σ = σ} ⊢Δ [σ] =
  let [Indσ] = proj₁ ([Ind] ⊢Δ [σ])
      pos = ctrArgsPos {ind = ind} {j = j} eq
      [args]σ = applyAllᵛ [Γ] ⊢Δ [σ] [args]
      ⊢argsσ = escapeArgs [args]σ
      [ctr] = ctrTerm [Indσ] ind∈ eq ⊢argsσ (indArgs pos [args]σ)
  in  PE.subst (λ t → _ ⊩⟨ _ ⟩ t ∷ Ind i ^ [ ! , ι ⁰ ] / [Indσ])
               (PE.sym (subst-ctr σ i j args))
               [ctr]
    , (λ {σ′} [σ′] [σ≡σ′] →
         let ⊢argsσ′ = escapeArgs (applyAllᵛ [Γ] ⊢Δ [σ′] [args])
             [args]≡ = applyAllEqᵛ [Γ] ⊢Δ [σ] [σ′] [σ≡σ′] [args]
             [ctr≡] = ctrEqTerm [Indσ] ind∈ eq ⊢argsσ ⊢argsσ′ (indArgsEq pos [args]≡)
         in  PE.subst₂ (λ t u → _ ⊩⟨ _ ⟩ t ≡ u ∷ Ind i ^ [ ! , ι ⁰ ] / [Indσ])
                       (PE.sym (subst-ctr σ i j args))
                       (PE.sym (subst-ctr σ′ i j args))
                       [ctr≡])
  where
    i = SU.SInd.name ind
