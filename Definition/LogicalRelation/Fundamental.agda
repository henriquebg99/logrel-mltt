import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Fundamental (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open import Definition.LogicalRelation.ShapeView senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.EquivEq senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Ind senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.IndRect senv swf equivs
open import Definition.Typed.Weakening senv equivs using (subst-emb-fwd; subst-emb-bwd)
open EqRelSet {{...}}
open import Definition.Untyped senv
open import Definition.Untyped.Properties senv
open import Definition.Typed senv equivs 
open import Definition.Typed.Properties senv equivs
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.Irrelevance senv equivs
open import Definition.LogicalRelation.Properties senv equivs
open import Definition.LogicalRelation.Substitution senv equivs
open import Definition.LogicalRelation.Substitution.Properties senv equivs
open import Definition.LogicalRelation.Substitution.Conversion senv equivs
open import Definition.LogicalRelation.Substitution.Reduction senv equivs
open import Definition.LogicalRelation.Substitution.Reflexivity senv equivs
open import Definition.LogicalRelation.Substitution.ProofIrrelevance senv equivs
open import Definition.LogicalRelation.Substitution.MaybeEmbed senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Nat senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Natrec senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Empty senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Universe senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Pi senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Id senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Cast senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.CastRefl senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.CastPi senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Lambda senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Application senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Fst senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Snd senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Transp senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.IdRefl senv equivs
open import Definition.LogicalRelation.Fundamental.Variable senv equivs
import Definition.LogicalRelation.Substitution.ProofIrrelevance senv equivs as PI
import Definition.LogicalRelation.Substitution.Irrelevance senv equivs as S
open import Definition.LogicalRelation.Substitution.Weakening senv equivs
open import Definition.LogicalRelation.Substitution.Escape senv equivs
open import Tools.Product
open import Tools.Unit
open import Tools.Nat
open import Tools.List using (All; All₂; []ₐ; _∷ₐ_; []; List; length; map; _++_; nth-map; all∈; All₂-length) renaming (_∷_ to _List∷_)
open import Tools.Maybe using (just)
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)
import Definition.SUntyped as SU
open import Definition.LogicalRelation.EquivRed senv equivs
open import Definition.Typed.IndRectCong senv swf equivs using (indRectBranchTyListCong)
  -- Fundamental theorem for contexts.
valid : ∀ {Γ} → ⊢ Γ → ⊩ᵛ Γ
fundamental : ∀ {Γ A rA} (⊢A : Γ ⊢ A ^ rA) → Σ (⊩ᵛ Γ) (λ [Γ] → Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ])
fundamentalEq : ∀{Γ A B rA} → Γ ⊢ A ≡ B ^ rA
              → ∃  λ ([Γ] : ⊩ᵛ Γ)
              → ∃₂ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ]) ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ rA / [Γ])
              → Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ B ^ rA / [Γ] / [A]
fundamentalTerm : ∀{Γ A rA t} → Γ ⊢ t ∷ A ^ rA
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ])
    → Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ rA / [Γ] / [A]
fundamentalTermEq : ∀{Γ A t t′ rA} → Γ ⊢ t ≡ t′ ∷ A ^ rA
                    → ∃ λ ([Γ] : ⊩ᵛ Γ)
                    → [ Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t′ ∷ A ^ rA / [Γ] ]
fundamentalAllInd : ∀ {Γ ind j Ts args}
    → ([Γ] : ⊩ᵛ Γ)
    → ([Ind] : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ])
    → SU.ctrArgsTypeList ind j PE.≡ just Ts
    → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
    → All (λ a → Γ ⊩ᵛ⟨ ∞ ⟩ a ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind]) args
fundamentalAllMethods : ∀ {Γ ind P rG lG ms}
    → ([Γ] : ⊩ᵛ Γ)
    → Γ ⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ]
    → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ rG , ι lG ] / [Γ])
                    → Γ ⊩ᵛ⟨ ∞ ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
           ms (indRectBranchTyList ind P rG lG)

-- Substituted terms are well-formed (clone of substitutionTerm, which lives in
-- a module that imports this one).
{-# TERMINATING #-}
subTerm : ∀ {Γ Δ σ t A rA}
        → ([Γ] : ⊩ᵛ Γ)
        → (⊢Δ : ⊢ Δ)
        → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
        → Γ ⊢ t ∷ A ^ rA
        → Δ ⊢ subst σ t ∷ subst σ A ^ rA

-- Substitution of well-typed constructor argument lists.
substAll-ctrArgs : ∀ {Γ Δ σ Ts args}
                 → ([Γ] : ⊩ᵛ Γ)
                 → (⊢Δ : ⊢ Δ)
                 → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                 → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
                 → Δ ⊢All map (subst σ) args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]

-- Substituted type equalities are well-formed (clone of substitutionEq, which
-- lives in a module that imports this one).
subTypeEq : ∀ {Γ Δ σ A B rA}
          → (⊢Δ : ⊢ Δ)
          → Δ ⊢ˢ σ ∷ Γ
          → Γ ⊢ A ≡ B ^ rA
          → Δ ⊢ subst σ A ^ rA × Δ ⊢ subst σ A ≡ subst σ B ^ rA

-- Substitution of well-typed IndRect method lists.
substAll-indRectBranch : ∀ {Γ Δ σ ind P rG lG ms}
                       → ([Γ] : ⊩ᵛ Γ)
                       → (⊢Δ : ⊢ Δ)
                       → ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                       → Γ ⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ]
                       → Δ ⊢All map (subst σ) ms ∷ indRectBranchTyList ind (subst (liftSubst σ) P) rG lG ^ [ rG , ι lG ]


abstract
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]

  -- Fundamental theorem for types.

  fundamental (Uⱼ x) = valid x , maybeEmbᵛ {A = Univ _ _} (valid x) (Uᵛ ∞< (valid x))
  fundamental (univ {A} ⊢A) with fundamentalTerm ⊢A
  fundamental (univ {A} ⊢A) | [Γ] , [U] , [A] =
              [Γ] , maybeEmbᵛ {A = A} [Γ] (univᵛ {A} [Γ] (≡is≤ PE.refl) [U] [A])

  -- Fundamental theorem for type equality.
  fundamentalEq (univ {A} {B} x) with fundamentalTermEq x
  fundamentalEq (univ {A} {B} x) | [Γ] , modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = maybeEmbᵛ {A = A} [Γ] (univᵛ {A} [Γ] (≡is≤ PE.refl) [U] [t])
        [B] = maybeEmbᵛ {A = B} [Γ] (univᵛ {B} [Γ] (≡is≤ PE.refl) [U] [u])
    in  [Γ] , [A] , [B]
    ,   (λ ⊢Δ [σ] → univEqEq (proj₁ ([U] ⊢Δ [σ]))
                             (proj₁ ([A] ⊢Δ [σ]))
                             ([t≡u] ⊢Δ [σ]))
  fundamentalEq (refl D) =
    let [Γ] , [B] = fundamental D
    in  [Γ] , [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq (sym A≡B) with fundamentalEq A≡B
  fundamentalEq (sym A≡B) | [Γ] , [B] , [A] , [B≡A] =
    [Γ] , [A] , [B]
        , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ]))
                            (proj₁ ([A] ⊢Δ [σ]))
                            ([B≡A] ⊢Δ [σ]))
  fundamentalEq (trans {A} {B₁} {B} A≡B₁ B₁≡B)
    with fundamentalEq A≡B₁ | fundamentalEq B₁≡B
  fundamentalEq (trans {A} {B₁} {B} A≡B B≡C) | [Γ] , [A] , [B₁] , [A≡B₁]
    | [Γ]₁ , [B₁]₁ , [B] , [B₁≡B] =
      [Γ] , [A] , S.irrelevance {A = B} [Γ]₁ [Γ] [B]
          , (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
               in  transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ]))
                           (proj₁ ([B] ⊢Δ [σ]′)) ([A≡B₁] ⊢Δ [σ])
                           (irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ]′))
                                          (proj₁ ([B₁] ⊢Δ [σ]))
                                          ([B₁≡B] ⊢Δ [σ]′)))

-- Fundamental theorem for terms.
  fundamentalTerm (ℕⱼ x) = valid x , maybeEmbᵛ {A = Univ _ _} (valid x) (Uᵛ emb< (valid x)) ,  maybeEmbTermᵛ {A = Univ _ _} {t = ℕ} (valid x) (Uᵛ emb< (valid x)) (ℕᵗᵛ (valid x))
  fundamentalTerm (Emptyⱼ ⊢Γ) = let [Γ] = valid ⊢Γ
                                    [U] = Uᵛ (proj₂ (levelBounded _)) [Γ]
                                 in [Γ] , maybeEmbᵛ {A = Univ _ _} [Γ] [U] , maybeEmbTermᵛ {A = Univ _ _} {t = sEmpty} [Γ] [U] (Emptyᵗᵛ [Γ] (proj₂ (levelBounded _)))
  fundamentalTerm (Πⱼ_▹_▹_▹_ {F} {rF} {lF} {G} {lG} {r = !} {lΠ} l! l% ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G | l! PE.refl
  ... | [Γ] , [UF] , [F]ₜ | [Γ]₁ ∙ [F] , [UG] , [G]ₜ | lF< , lG< =
    let [UF]′ = maybeEmbᵛ {A = Univ rF _} [Γ]₁ (Uᵛ (proj₂ (levelBounded lF)) [Γ]₁)
        [UΠ]  = maybeEmbᵛ {A = Univ ! _} [Γ]₁ (Uᵛ (proj₂ (levelBounded lΠ)) [Γ]₁)
        [F]′  = maybeEmbᵛ {A = F} [Γ]₁ [F]
        [UG]′ : _ ⊩ᵛ⟨ ∞ ⟩ Univ ! lG ^ [ ! , next lG ] / _∙_ {A = F} [Γ]₁ [F]′
        [UG]′ = λ {Δ} {σ} → S.irrelevance {A = Univ ! lG} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ}) {Δ} {σ}
        [F]ₜ′ = S.irrelevanceTerm {A = Univ rF _} {t = F} [Γ] [Γ]₁ [UF] [UF]′ [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ}) (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ
    in  [Γ]₁ , [UΠ] 
    , 
      Πᵗᵛ {F} {G} {rF} {lF} {lG} {lΠ} lF< lG< [Γ]₁ [F]′ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [F]ₜ′ [G]ₜ′
  fundamentalTerm (Πⱼ_▹_▹_▹_ {F} {rF} {lF} {G} {lG = ⁰} {r = %} {l = ⁰} lF< lG< ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [UF] , [F]ₜ | [Γ]₁ ∙ [F] , [UG] , [G]ₜ =
    let [UF]′ = maybeEmbᵛ {A = Univ rF _} [Γ]₁ (Uᵛ (proj₂ (levelBounded lF)) [Γ]₁)
        [UΠ]  = maybeEmbᵛ {A = Univ % _} [Γ]₁ (Uᵛ (proj₂ (levelBounded ⁰)) [Γ]₁)
        [F]′  = maybeEmbᵛ {A = F} [Γ]₁ [F]
        [UG]′ : _ ⊩ᵛ⟨ ∞ ⟩ Univ % ⁰ ^ [ ! , next ⁰ ] / _∙_ {A = F} [Γ]₁ [F]′
        [UG]′ = λ {Δ} {σ} → S.irrelevance {A = SProp} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ}) {Δ} {σ}
        [F]ₜ′ = S.irrelevanceTerm {A = Univ rF _} {t = F} [Γ] [Γ]₁ [UF] [UF]′ [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ}) (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ
    in  [Γ]₁ , [UΠ] 
    , 
      Πirrᵗᵛ {F} {G} {rF} {lF} [Γ]₁ [F]′ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [F]ₜ′ [G]ₜ′
  fundamentalTerm (Πⱼ_▹_▹_▹_ {F} {rF} {lF} {G} {lG = ¹} {r = %} {l} lF< lG< ⊢F ⊢G) = let e , _ = lG< PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))
  fundamentalTerm (Πⱼ_▹_▹_▹_ {F} {rF} {lF} {G} {lG} {r = %} {l = ¹} lF< lG< ⊢F ⊢G) = let _ , e = lG< PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))

  fundamentalTerm (Idⱼ {A} {l} {t} {u} ⊢A ⊢t ⊢u)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  ... | [Γ] , [UA] , [A]ₜ | [Γt] , [At] , [t]ₜ | [Γu] , [Au] , [u]ₜ =
    let [SProp] = maybeEmbᵛ {A = SProp} [Γu] (Uᵛ (proj₂ (levelBounded ⁰)) [Γu])
        [t]ₜ′ = S.irrelevanceTerm {A = A} {t = t} [Γt] [Γu] [At] [Au] [t]ₜ
        [UA]′ = maybeEmbᵛ {A = Univ _ _} [Γu] (λ {Δ} {σ} → Uᵛ <next [Γu] {Δ} {σ})
        [A]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γu] (λ {Δ} {σ} → [UA] {Δ} {σ}) (λ {Δ} {σ} → [UA]′ {Δ} {σ}) [A]ₜ
    in [Γu] , [SProp] , Idᵗᵛ {A = A} {t = t} {u = u } [Γu] [Au] [t]ₜ′ [u]ₜ [A]ₜ′

  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , fundamentalVar x∷A (valid ⊢Γ)
  fundamentalTerm (lamⱼ {F} {r = !} {l} {rF} {lF} {G} {lG} {t} l! l% ⊢F ⊢t)
    with fundamental ⊢F | fundamentalTerm ⊢t  | l! PE.refl
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] | lF< , lG< =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]′ = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]′ [t]
    in  [Γ] , Πᵛ {F} {G} lF< lG< [Γ] [F] [G]′
    ,   lamᵛ {F} {G} {rF} {lF} {lG} {l} {t} lF< lG< [Γ] [F] [G]′ [t]′
  fundamentalTerm (lamⱼ {F} {r = %} {l = ⁰} {rF} {lF} {G} {lG = ⁰} {t} lF< lG< ⊢F ⊢t)
    with fundamental ⊢F | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]′ = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]′ [t]
    in  [Γ] , Πirrᵛ {F} {G} [Γ] [F] [G]′
    ,   lamirrᵛ {F} {G} {rF} {lF} {t} [Γ] [F] [G]′ [t]′
  fundamentalTerm (lamⱼ {F} {r = %} {l = ⁰} {rF} {lF} {G} {lG = ¹} {t} lF< lG< ⊢F ⊢t) = let e , _ = lG< PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))
  fundamentalTerm (lamⱼ {F} {r = %} {l = ¹} {rF} {lF} {G} {lG} {t} lF< lG< ⊢F ⊢t) = let _ , e = lG< PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))
  fundamentalTerm (_▹_▹_▹_∘ⱼ_ {g} {a} {F} {rF} {lF} {G} {lG} {r = !} {l} _ [F] DG Dt Du)
    with fundamentalTerm DG | fundamentalTerm Dt | fundamentalTerm Du 
  ... | [Γ]' , [UG] , [G] | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]′ = S.irrelevance {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} [Γ] [Γ]₁ [ΠFG]
        [G]′ = maybeEmbᵛ {A = G} [Γ]'
               (univᵛ {A = G} [Γ]' (≡is≤ PE.refl)
               (λ {Δ} {σ} → [UG] {Δ} {σ}) [G])
        [G]′′ = S.irrelevance {A = G} [Γ]' (_∙_ {A = F} [Γ]₁ [F])  [G]′
        [t]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [t]
        [G[t]] = substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]′ [u]
        [t∘u] = appᵛ {F} {G} {rF} {lF} {lG} {l} {g} {a} [Γ]₁ [F] [G]′′ [ΠFG]′ [t]′ [u]
    in  [Γ]₁ , [G[t]] , [t∘u]
  fundamentalTerm (_▹_▹_▹_∘ⱼ_ {g} {a} {F} {rF} {lF} {G} {lG = ⁰} {r = %} {lΠ = ⁰} _ [F] DG Dt Du)
    with fundamentalTerm DG | fundamentalTerm Dt | fundamentalTerm Du 
  ... | [Γ]' , [UG] , [G] | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]′ = S.irrelevance {A = Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ %} [Γ] [Γ]₁ [ΠFG]
        [G]′ = maybeEmbᵛ {A = G} [Γ]'
               (univᵛ {A = G} [Γ]' (≡is≤ PE.refl)
               (λ {Δ} {σ} → [UG] {Δ} {σ}) [G])
        [G]′′ = S.irrelevance {A = G} [Γ]' (_∙_ {A = F} [Γ]₁ [F])  [G]′
        [t]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ %} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [t]
        [G[t]] = substS {F} {G} {a} [Γ]₁ [F] [G]′′ [u]
        [t∘u] = appirrᵛ {F} {G} {rF} {lF} {g} {a} [Γ]₁ [F] [G]′′ [ΠFG]′ [t]′ [u]
    in  [Γ]₁ , [G[t]] , [t∘u]
  fundamentalTerm (_▹_▹_▹_∘ⱼ_ {g} {a} {F} {rF} {lF} {G} {lG = ¹} {r = %} {lΠ} l% [F] DG Dt Du) = let e , _ = l% PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))
  fundamentalTerm (_▹_▹_▹_∘ⱼ_ {g} {a} {F} {rF} {lF} {G} {lG} {r = %} {lΠ = ¹} l% [F] DG Dt Du) = let _ , e = l% PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))
  fundamentalTerm (zeroⱼ x) = valid x , ℕᵛ (valid x) , zeroᵛ {l = ∞} (valid x)
  fundamentalTerm (sucⱼ {n} t) with fundamentalTerm t
  fundamentalTerm (sucⱼ {n} t) | [Γ] , [ℕ] , [n] =
    [Γ] , [ℕ] , sucᵛ {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrecⱼ {G} {rG} {lG} {s} {z} {n} rGlG ⊢G ⊢z ⊢s ⊢n)
    with fundamental ⊢G | fundamentalTerm ⊢z | fundamentalTerm ⊢s
       | fundamentalTerm ⊢n
  ... | [Γ] , [G] | [Γ]₁ , [G₀] , [z] | [Γ]₂ , [G₊] , [s] | [Γ]₃ , [ℕ] , [n] =
    let sType = Π ℕ ^ ! ° ⁰ ▹ (G ^ rG ° _  ▹▹ G [ suc (var 0) ]↑ ° _  ° lG ^ rG) ° _ ° lG ^ rG
        [Γ]′ = [Γ]₃
        [G]′ = S.irrelevance {A = G} [Γ] ([Γ]′ ∙ [ℕ]) [G]
        [G₀]′ = S.irrelevance {A = G [ zero ]} [Γ]₁ [Γ]′ [G₀]
        [G₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]′ [G₊]
        [Gₙ]′ = substS {F = ℕ} {G = G} {t = n} [Γ]′ [ℕ] [G]′ [n]
        [z]′ = S.irrelevanceTerm {A = G [ zero ]} {t = z} [Γ]₁ [Γ]′
                                 [G₀] [G₀]′ [z]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]′ [G₊] [G₊]′ [s]
    in  [Γ]′ , [Gₙ]′
    ,   natrecᵛ {G} {rG} {lG} {z} {s} {n} rGlG [Γ]′ [ℕ] [G]′ [G₀]′ [G₊]′ [Gₙ]′ [z]′ [s]′ [n]

  fundamentalTerm (fstⱼ {A} {A'} {rA} {B} {B'} {e} ⊢A ⊢B ⊢A' ⊢B' ⊢e)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B' | fundamentalTerm ⊢e
  ... | [Γ] , [UA] , [A]ₜ | [Γ]₁ ∙ [A]₁ , [UB] , [B]ₜ | [Γ]' , [UA'] , [A']ₜ | [Γ]₁' ∙ [A']₁ , [UB'] , [B']ₜ | [Γe] , [Id] , [e]ₜ =
    let [A]′  = S.irrelevance {A = A} [Γ] [Γ]₁' (maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ))
        [A']′  = S.irrelevance {A = A'} [Γ]' [Γ]₁' (maybeEmbᵛ {A = A'} [Γ]' (univᵛ {A = A'} [Γ]' (≡is≤ PE.refl) [UA'] [A']ₜ))
        [UB]′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [UB']′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ})
        [U] = maybeEmbᵛ {A = Univ rA _} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]₁' [UA] [U] [A]ₜ
        [A']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A'} [Γ]' [Γ]₁' [UA'] [U] [A']ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B}  (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [B']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B'} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ
        [UA]' = maybeEmbᵛ {A = Univ rA ⁰} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [U0] = maybeEmbᵛ {A = U ⁰} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [Id]′ = S.irrelevance {A = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !)} [Γe] [Γ]₁' [Id]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !)} {t = e} [Γe] [Γ]₁' [Id]
                                   [Id]′ [e]ₜ
        [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ]₁' (λ {Δ} {σ} → [UA]' {Δ} {σ}) [A]ₜ′ [A']ₜ′ 
    in [Γ]₁' , [IdAA'] , fstᵛ {A = A} {B = B} {A' = A'} {B' = B'} {e = e} {rA = rA} [Γ]₁' [A]′ [A']′ (λ {Δ} {σ} → [UB]′ {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ})
                         [A]ₜ′ [B]ₜ′ [A']ₜ′ [B']ₜ′ [Id]′ [e]ₜ′                         
  fundamentalTerm {Γ} (sndⱼ {A} {A'} {rA} {B} {B'} {e} ⊢A ⊢B ⊢A' ⊢B' ⊢e)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B' | fundamentalTerm ⊢e
  ... | [Γ] , [UA] , [A]ₜ | [Γ]₁ ∙ [A]₁ , [UB] , [B]ₜ | [Γ]' , [UA'] , [A']ₜ | [Γ]₁' ∙ [A']₁ , [UB'] , [B']ₜ | [Γe] , [Id] , [e]ₜ =
    let [A]′  = S.irrelevance {A = A} [Γ] [Γ]₁' (maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ))
        [A']′  = S.irrelevance {A = A'} [Γ]' [Γ]₁' (maybeEmbᵛ {A = A'} [Γ]' (univᵛ {A = A'} [Γ]' (≡is≤ PE.refl) [UA'] [A']ₜ))
        [UB]′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [UB']′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ})
        [U] = maybeEmbᵛ {A = Univ rA _} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]₁' [UA] [U] [A]ₜ
        [A']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A'} [Γ]' [Γ]₁' [UA'] [U] [A']ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B}  (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [B']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B'} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ
        [UA]' = maybeEmbᵛ {A = Univ rA ⁰} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [U0] = maybeEmbᵛ {A = U ⁰} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [Id]′ = S.irrelevance {A = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !)} [Γe] [Γ]₁' [Id]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !)} {t = e} [Γe] [Γ]₁' [Id]
                                   [Id]′ [e]ₜ
        [ΓA'] = (_∙_ {Γ} {A'} [Γ]₁' [A']′)
        [wA']' = wk1ᵛ {A = A'} {F = A'} [Γ]₁' [A']′ [A']′
        [var0]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / [wA']'
        [var0]ₜ = proj₂ (fundamentalVar here [ΓA']) 
        [IdBB'] = Id-U-ΠΠ-resᵗᵛ {A} {B} {A'} {B'} {e} [Γ]₁' [A]′ [A']′
                                       (λ {Δ} {σ} → [UB]′ {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ})
                                       [A]ₜ′ [B]ₜ′ [A']ₜ′ [B']ₜ′ [Id]′ [e]ₜ′ [var0]ₜ 
    in [Γ]₁' , [IdBB'] , sndᵛ {A = A} {B = B} {A' = A'} {B' = B'} {e = e} {rA = rA} [Γ]₁' [A]′ [A']′ (λ {Δ} {σ} → [UB]′ {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ})
                         [A]ₜ′ [B]ₜ′ [A']ₜ′ [B']ₜ′ [Id]′ [e]ₜ′

  fundamentalTerm {Γ} (Idreflⱼ {A} {l} {t} ⊢t)
    with fundamentalTerm ⊢t 
  ... | [Γ] , [A] , [t]  =
    let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
    in [Γ] , [Id] , Idreflᵛ {Γ} {A} {l} {t} [Γ] [A] [t]

  fundamentalTerm (equiv-eqⱼ ⊢Γ) =
    let [Γ] = valid ⊢Γ
        [U0] = maybeEmbᵛ {A = U ⁰} [Γ] (Uᵛ emb< [Γ])
        [ℕ]  = maybeEmbTermᵛ {A = U ⁰} {t = ℕ} [Γ] [U0] (ℕᵗᵛ [Γ])
        [Id] = Idᵛ {A = U ⁰} {t = ℕ} {u = ℕ} [Γ] [U0] [ℕ] [ℕ]
    in [Γ] , [Id] , equivEqᵛ [Γ]

  fundamentalTerm (transpⱼ {A} {l} {P} {t} {s} {u} {e} ⊢A ⊢P ⊢t ⊢s ⊢u ⊢e)
    with fundamental ⊢A | fundamental ⊢P  | fundamentalTerm ⊢t | fundamentalTerm ⊢s | fundamentalTerm ⊢u | fundamentalTerm ⊢e
  ... | [ΓA] , [A] | [ΓP] ∙ [A]' , [P] | [Γt] , [At] , [t] | [Γs] , [Pt] , [s] | [Γu] , [Au] , [u] | [Γe] , [Id] , [e] =
    let [A]′ = S.irrelevance {A = A} [ΓA] [Γe] [A]
        [P]′ = S.irrelevance {A = P} (_∙_ {A = A} [ΓP] [A]') (_∙_ {A = A} [Γe] [A]′) [P]
        [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γt] [Γe] [At] [A]′ [t]
        [u]′ = S.irrelevanceTerm {A = A} {t = u} [Γu] [Γe] [Au] [A]′ [u]
        [Pt]′ = substS {A} {P} {t} [Γe] [A]′ [P]′ [t]′
        [s]′ = S.irrelevanceTerm {A = P [ t ] } {t = s} [Γs] [Γe] [Pt] [Pt]′ [s]
    in [Γe] ,  substS {A} {P} {u} [Γe] [A]′ [P]′ [u]′ , transpᵗᵛ {A} {P} {l} {t} {s} {u} {e} [Γe] [A]′ [P]′ [t]′ [s]′ [u]′ [Id] [e]
  fundamentalTerm (castⱼ {A} {B} {r} {e} {t} ⊢A ⊢B ⊢e ⊢t)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B  | fundamentalTerm ⊢e  | fundamentalTerm ⊢t
  ... | [ΓA] , [UA] , [A]ₜ | [ΓB] , [UB] , [B]ₜ | [Γe] , [Id] , [e]ₜ | [Γ]₁ , [At] , [t]ₜ =
    let [UA]′ = S.irrelevance {A = Univ _ _} [ΓA] [Γ]₁ [UA] 
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [Γ]₁ [UA] [UA]′ [A]ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} [ΓB] [Γ]₁ [UB] [UA]′ [B]ₜ
        [B] = maybeEmbᵛ {A = B} [Γ]₁ (univᵛ {A = B} [Γ]₁ (≡is≤ PE.refl) [UA]′ [B]ₜ′)
        [Id]′ = S.irrelevance {A = Id (Univ r _) A B} [Γe] [Γ]₁ [Id] 
        [e]ₜ′  = S.irrelevanceTerm {A = Id (Univ r _) A B} {t = e} [Γe] [Γ]₁ [Id] [Id]′ [e]ₜ
     in [Γ]₁ , [B] , castᵗᵛ {A} {B} {r} {t} {e} [Γ]₁ [UA]′ [A]ₜ′ [B]ₜ′ [At] [B] [t]ₜ [Id]′ [e]ₜ′

  fundamentalTerm (Emptyrecⱼ {A} {lA} {rA} {n} ⊢A ⊢n)
    with fundamental ⊢A | fundamentalTerm ⊢n
  ... | [Γ] , [A] | [Γ]′ , [Empty] , [n] =
    let [A]′ = S.irrelevance {A = A} [Γ] [Γ]′ [A]
    in [Γ]′ , [A]′ , Emptyrecᵛ {A} {rA} {lA} {n} [Γ]′ [Empty] [A]′ [n]
  fundamentalTerm (Indⱼ x) = valid x , maybeEmbᵛ {A = Univ _ _} (valid x) (Uᵛ emb< (valid x)) , maybeEmbTermᵛ {A = Univ _ _} {t = Ind _} (valid x) (Uᵛ emb< (valid x)) (Indᵗᵛ (valid x))
  fundamentalTerm (Ctrⱼ {ind} {j} {args} {Ts} ⊢Γ ind∈ eq args∈) =
    let i = (SU.SInd.name ind)
        [Γ] = valid ⊢Γ
        [Ind] = Indᵛ {i = i} {l = ∞} [Γ]
        [args] = fundamentalAllInd {ind = ind} {j = j} {Ts = Ts} {args = args} [Γ] [Ind] eq args∈
    in  [Γ] , [Ind]
    ,   ctrᵛ {ind = ind} {j = j} {args = args} {Ts = Ts} {l = ∞} [Γ] [Ind] ind∈ eq args∈ [args]
  fundamentalTerm (IndRectⱼ {ind} {P} {rG} {lG} {t} {ms} abs ind∈ ⊢P ⊢t ⊢ms)
    with fundamental ⊢P | fundamentalTerm ⊢t
  ... | [ΓP] , [P] | [Γt] , [Indt] , [t] =
    let i = (SU.SInd.name ind)
        [Γ] = [Γt]
        [Ind] = Indᵛ {i = i} {l = ∞} [Γ]
        [Γ∙Ind] = _∙_ {A = Ind i} [Γ] [Ind]
        [P]′ = S.irrelevance {A = P} [ΓP] [Γ∙Ind] [P]
        [t]′ = S.irrelevanceTerm {A = Ind i} {t = t} [Γ] [Γ] [Indt] [Ind] [t]
        [Pt] = substS {F = Ind i} {G = P} {t = t} [Γ] [Ind] [P]′ [t]′
        [ms] = fundamentalAllMethods {ind = ind} {P = P} {rG = rG} {lG = lG} {ms = ms} [Γ] ⊢ms
    in  [Γ] , [Pt]
    ,   IndRectᵛ {ind = ind} {P = P} {rG = rG} {lG = lG} {t = t} {ms = ms} {l = ∞}
                 abs [Γ] ind∈ [Ind] [P]′ [t]′ [Pt] ⊢ms [ms]
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A)
    with fundamentalTerm ⊢t | fundamentalEq A′≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A) | [Γ] , [A′] , [t]
    | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [Γ]′ = [Γ]₁
          [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]′ [A′] [A′]₁ [t]
      in  [Γ]′ , [A]
      ,   convᵛ {t} {A} {B} [Γ]′ [A′]₁ [A] [A′≡A] [t]′
  fundamentalTerm (univ 0<1 ⊢Γ) = let [Γ] = valid ⊢Γ
                                  in [Γ] , (Uᵛ ∞< [Γ] , Uᵗᵛ [Γ])

  -- Fundamental theorem for term equality.
  fundamentalTermEq (refl D) with fundamentalTerm D
  ... | [Γ] , [A] , [t] =
    [Γ] , modelsTermEq [A] [t] [t]
                       (λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                              (proj₁ ([t] ⊢Δ [σ])))
  fundamentalTermEq (sym D) with fundamentalTermEq D
  fundamentalTermEq (sym D) | [Γ] , modelsTermEq [A] [t′] [t] [t′≡t] =
    [Γ] , modelsTermEq [A] [t] [t′]
                       (λ ⊢Δ [σ] → symEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                             ([t′≡t] ⊢Δ [σ]))
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
    with fundamentalTermEq t≡u | fundamentalTermEq u≡t′
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u]
    | [Γ]₁ , modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ =
      let [r]′ = S.irrelevanceTerm {A = A} {t = r} [Γ]₁ [Γ] [A]₁ [A] [u]₁
      in  [Γ] , modelsTermEq [A] [t] [r]′
                  (λ ⊢Δ [σ] →
                     let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
                         [t≡u]₁′ = irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ]′))
                                                     (proj₁ ([A] ⊢Δ [σ]))
                                                     ([t≡u]₁ ⊢Δ [σ]′)
                     in  transEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                     ([t≡u] ⊢Δ [σ]) [t≡u]₁′)
  fundamentalTermEq (conv {A} {B} {r} {t} {u} t≡u A′≡A)
    with fundamentalTermEq t≡u | fundamentalEq A′≡A
  fundamentalTermEq (conv {A} {B} {r} {t} {u} t≡u A′≡A)
    | [Γ] , modelsTermEq [A′] [t] [u] [t≡u] | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]₁ [A′] [A′]₁ [t]
          [u]′ = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ]₁ [A′] [A′]₁ [u]
          [t]″ = convᵛ {t} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [t]′
          [u]″ = convᵛ {u} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [u]′
      in  [Γ]₁
      ,   modelsTermEq [A] [t]″ [u]″
            (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]
                   [t≡u]′ = irrelevanceEqTerm (proj₁ ([A′] ⊢Δ [σ]′))
                                              (proj₁ ([A′]₁ ⊢Δ [σ]))
                                              ([t≡u] ⊢Δ [σ]′)
               in  convEqTerm₁ (proj₁ ([A′]₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))
                               ([A′≡A] ⊢Δ [σ]) [t≡u]′)
  fundamentalTermEq (Π-cong {E} {F} {G} {H} {rF} {lF} {rG = !} {lG} {lΠ} l! l% ⊢F F≡H G≡E)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E | l! PE.refl
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ | lF< , lG< =
    let [U]′  = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ]) 
        [UΠ] = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
        [F]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = maybeEmbᵛ {A = H} [Γ] (univᵛ {A = H} [Γ] (≡is≤ PE.refl) [U]′ [H]ₜ′)
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = S.irrelevance {A = Univ _ _} [Γ]₂ ([Γ] ∙ [F]) [U]₁ 
        [U]₂′ = S.irrelevanceLift {A = Univ _ _} {F = F} {H = H} [Γ] [F] [H] [F≡H] (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = Univ _ _} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H]
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
                  (S.irrelevanceTerm {A = Univ _ _} {t = E} [Γ]₂ ([Γ] ∙ [F])
                                     [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] [U]′ [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [UΠ] -- looks like [U]′ but the implicits are different
          (Πᵗᵛ {F} {G} lF< lG< [Γ] [F] (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [F]ₜ′ [G]ₜ′ ) 
          (Πᵗᵛ {H} {E} lF< lG< [Γ] [H] (λ {Δ} {σ} → [U]₂′ {Δ} {σ}) [H]ₜ′ [E]ₜ′) 
          (Π-congᵗᵛ {F} {G} {H} {E} lF< lG< [Γ] [F] [H]
                    (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) (λ {Δ} {σ} → [U]₂′ {Δ} {σ})
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′) 
  fundamentalTermEq (Π-cong {E} {F} {G} {H} {rF} {lF} {rG = %} {lG = ⁰} {l = ⁰} l! l% ⊢F F≡H G≡E)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E 
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]′  = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ]) 
        [UΠ] = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
        [F]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = maybeEmbᵛ {A = H} [Γ] (univᵛ {A = H} [Γ] (≡is≤ PE.refl) [U]′ [H]ₜ′)
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = S.irrelevance {A = Univ _ _} [Γ]₂ ([Γ] ∙ [F]) [U]₁ 
        [U]₂′ = S.irrelevanceLift {A = Univ _ _} {F = F} {H = H} [Γ] [F] [H] [F≡H] (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = Univ _ _} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H]
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
                  (S.irrelevanceTerm {A = Univ _ _} {t = E} [Γ]₂ ([Γ] ∙ [F])
                                     [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] [U]′ [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [UΠ] -- looks like [U]′ but the implicits are different
          (Πirrᵗᵛ {F} {G} [Γ] [F] (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [F]ₜ′ [G]ₜ′ ) 
          (Πirrᵗᵛ {H} {E} [Γ] [H] (λ {Δ} {σ} → [U]₂′ {Δ} {σ}) [H]ₜ′ [E]ₜ′) 
          (Πirr-congᵗᵛ {F} {G} {H} {E} [Γ] [F] [H]
                    (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) (λ {Δ} {σ} → [U]₂′ {Δ} {σ})
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′) 
  fundamentalTermEq (Π-cong {E} {F} {G} {H} {rF} {lF} {rG = %} {lG = ¹} {l} l! l% ⊢F F≡H G≡E) = let e , _ = l% PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))
  fundamentalTermEq (Π-cong {E} {F} {G} {H} {rF} {lF} {rG = %} {lG} {l = ¹} l! l% ⊢F F≡H G≡E) = let _ , e = l% PE.refl in ⊥-elim (⁰≢¹ (PE.sym e))

  fundamentalTermEq (app-cong {a} {b} {f} {g} {F} {G} {rF} {lF} {lG} {l} f≡g a≡b)
    with fundamentalTermEq f≡g | fundamentalTermEq a≡b
  ... | [Γ] , modelsTermEq [ΠFG] [f] [g] [f≡g]
      | [Γ]₁ , modelsTermEq [F] [a] [b] [a≡b] =
    let [ΠFG]′ = S.irrelevance {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} [Γ] [Γ]₁ [ΠFG]
        [f]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = f} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f]
        [g]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [g]
        [f≡g]′ = S.irrelevanceEqTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = f} {u = g}
                                     [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f≡g]
        [G[a]] = substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]′ [a]
        [G[b]] = substSΠ {F} {G} {b} [Γ]₁ [F] [ΠFG]′ [b]
        [G[a]≡G[b]] = substSΠEq {F} {G} {F} {G} {a} {b} [Γ]₁ [F] [F] [ΠFG]′
                                [ΠFG]′ (reflᵛ {Π F ^ rF ° lF ▹ G ° lG ° l ^ !} [Γ]₁ [ΠFG]′) [a] [b] [a≡b]
    in  [Γ]₁ , modelsTermEq [G[a]]
                            (appᵛ {F} {G} {rF} {lF} {lG} {l} {f} {a} [Γ]₁ [F] (decompΠᵛ {F = F} {G = G} [Γ]₁ [F] [ΠFG]′) [ΠFG]′ [f]′ [a])
                            (conv₂ᵛ {g ∘ b ^ l} {G [ a ]} {G [ b ]} [Γ]₁
                                    [G[a]] [G[b]] [G[a]≡G[b]]
                                    (appᵛ {F} {G} {rF} {lF} {lG} {l} {g} {b}
                                          [Γ]₁ [F] (decompΠᵛ {F = F} {G = G} [Γ]₁ [F] [ΠFG]′) [ΠFG]′ [g]′ [b]))
                            (app-congᵛ {F} {G} {rF} {lF} {lG} {l} {f} {g} {a} {b}
                                       [Γ]₁ [F] (decompΠᵛ {F = F} {G = G} [Γ]₁ [F] [ΠFG]′) [ΠFG]′ [f≡g]′ [a] [b] [a≡b])
  fundamentalTermEq (β-red {a} {b} {F} {rF} {lF} {G} {lG} {l} l< l<' ⊢F ⊢b ⊢a)
    with fundamental ⊢F | fundamentalTerm ⊢b | fundamentalTerm ⊢a
  ... | [Γ] , [F] | [Γ]₁ , [G] , [b] | [Γ]₂ , [F]₁ , [a] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G]
        [b]′ = S.irrelevanceTerm {A = G} {t = b} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G] [G]′ [b]
        [G[a]] = substS {F} {G} {a} [Γ]₂ [F]₁ [G]′ [a]
        [b[a]] = substSTerm {F} {G} {a} {b} [Γ]₂ [F]₁ [G]′ [b]′ [a]
        [lam] , [eq] =
          redSubstTermᵛ {G [ a ]} {(lam F ▹ b ^ l) ∘ a ^ l} {b [ a ]} [Γ]₂
            (λ {Δ} {σ} ⊢Δ [σ] →
               let [liftσ] = liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ]
                   ⊢σF = escape (proj₁ ([F]₁ ⊢Δ [σ]))
                   ⊢σG = un-univ (escape (proj₁ ([G]′ (⊢Δ ∙ ⊢σF) [liftσ])))
                   ⊢σb = escapeTerm (proj₁ ([G]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                                       (proj₁ ([b]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                   ⊢σa = escapeTerm (proj₁ ([F]₁ ⊢Δ [σ]))
                                       (proj₁ ([a] ⊢Δ [σ]))
               in  PE.subst₂ (λ x y → _ ⊢ (lam (subst σ F) ▹ (subst (liftSubst σ) b) ^ _)
                                          ∘ (subst σ a) ^ _ ⇒ x ∷ y ^ _)
                             (PE.sym (singleSubstLift b a))
                             (PE.sym (singleSubstLift G a))
                             (β-red l< l<' ⊢σF ⊢σG ⊢σb ⊢σa))
                         [G[a]] [b[a]]
    in  [Γ]₂ , modelsTermEq [G[a]] [lam] [b[a]] [eq]
  fundamentalTermEq (η-eq {f} {g} {F} {rF} {lF} {lG} {l} {G} lF< lG< ⊢F ⊢t ⊢t′ t≡t′) with
    fundamental ⊢F | fundamentalTerm ⊢t |
    fundamentalTerm ⊢t′ | fundamentalTermEq t≡t′
  ... | [Γ] , [F] | [Γ]₁ , [ΠFG] , [t] | [Γ]₂ , [ΠFG]₁ , [t′]
      | [Γ]₃ , modelsTermEq [G] [t0] [t′0] [t0≡t′0] = 
    let [F]′ = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [G]′ = S.irrelevance {A = G} [Γ]₃ ([Γ]₁ ∙ [F]′) [G]
        [t′]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = g}
                                  [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG] [t′]
        [ΠFG]″ = Πᵛ {F} {G} lF< lG< [Γ]₁ [F]′ [G]′
        [t]″ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = f}
                                  [Γ]₁ [Γ]₁ [ΠFG] [ΠFG]″ [t]
        [t′]″ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = g}
                                   [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG]″ [t′]
        [t0≡t′0]′ = S.irrelevanceEqTerm {A = G} {t = wk1 f ∘ var 0 ^ l}
                                        {u = wk1 g ∘ var 0 ^ l}
                                        [Γ]₃ ([Γ]₁ ∙ [F]′) [G] [G]′ [t0≡t′0]
        [t≡t′] = η-eqᵛ {f} {g} {F} {G} lF< lG< [Γ]₁ [F]′ [G]′ [t]″ [t′]″ [t0≡t′0]′
        [t≡t′]′ = S.irrelevanceEqTerm {A = Π F ^ rF ° lF ▹ G ° lG ° l ^ !} {t = f} {u = g}
                                      [Γ]₁ [Γ]₁ [ΠFG]″ [ΠFG] [t≡t′] 
    in [Γ]₁ , modelsTermEq [ΠFG] [t] [t′]′ [t≡t′]′
  fundamentalTermEq (suc-cong x) with fundamentalTermEq x
  fundamentalTermEq (suc-cong {t} {u} x)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
      let [suct] = sucᵛ {n = t} [Γ] [A] [t]
          [sucu] = sucᵛ {n = u} [Γ] [A] [u]
      in  [Γ] , modelsTermEq [A] [suct] [sucu]
                             (λ ⊢Δ [σ] →
                                sucEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq {Γ} (ctr-cong {ind} {j} {args} {args'} {Ts} ⊢Γ ind∈ eq lens eqs) =
    let [Γ] , [args]ᵥ , [args']ᵥ , [eqs]ᵥ = go eqs
        [Ind] = Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Γ]
        posAll = all∈ (SU.ctrArgsTypesPositive ind j Ts eq)
        ⊢args = to⊢All [Γ] posAll [args]ᵥ lens
        ⊢args' = to⊢All [Γ] posAll [args']ᵥ (PE.trans (PE.sym (All₂-length eqs)) lens)
        [ctrₜ] = ctrᵛ {ind = ind} {j = j} {Ts = Ts} {l = ∞} [Γ] [Ind] ind∈ eq ⊢args [args]ᵥ
        [ctrᵤ] = ctrᵛ {ind = ind} {j = j} {Ts = Ts} {l = ∞} [Γ] [Ind] ind∈ eq ⊢args' [args']ᵥ
    in  [Γ]
    ,   modelsTermEq [Ind] [ctrₜ] [ctrᵤ]
                     (λ {Δ} {σ} ⊢Δ [σ] →
                        let [Indσ] = proj₁ ([Ind] ⊢Δ [σ])
                            [eqs]σ = applyAll₂ᵛ [Γ] [Ind] ⊢Δ [σ] [eqs]ᵥ
                        in  PE.subst₂ (λ t u → _ ⊩⟨ _ ⟩ t ≡ u ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Indσ])
                                      (PE.sym (subst-ctr σ (SU.SInd.name ind) j args))
                                      (PE.sym (subst-ctr σ (SU.SInd.name ind) j args'))
                                      (ctrEqTerm [Indσ] ind∈ eq
                                                 (substAll-ctrArgs {σ = σ} [Γ] ⊢Δ [σ] ⊢args)
                                                 (substAll-ctrArgs {σ = σ} [Γ] ⊢Δ [σ] ⊢args')
                                                 [eqs]σ))
    where

      emb-stype-pos : ∀ (T : SU.Type) → SU.isPositive (SU.SInd.name ind) T → emb-stype T PE.≡ Ind (SU.SInd.name ind)
      emb-stype-pos (SU.Ind j′) i≡i = PE.cong Ind (PE.sym i≡i)
      emb-stype-pos (SU.Arrow _ _) ()

      to⊢All : ∀ {Δ} {args Ts} ([Δ] : ⊩ᵛ Δ)
             → All (SU.isPositive (SU.SInd.name ind)) Ts
             → All (λ a → Δ ⊩ᵛ⟨ ∞ ⟩ a ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Δ] / Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Δ]) args
             → length args PE.≡ length Ts
             → Δ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
      to⊢All [Δ] []ₐ []ₐ _ = εⱼ
      to⊢All {Δ} {args = a List∷ as} {Ts = T List∷ Ts} [Δ] (pos ∷ₐ poss) ([a]ᵥ ∷ₐ ps) eq =
        let [Ind] = Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Δ]
            emb≡Ind = emb-stype-pos T pos
            ⊢Δ = soundContext [Δ]
            ⊢a = escapeTermᵛ [Δ] [Ind] [a]ᵥ
            ⊢Ind≡emb = PE.subst (λ T′ → Δ ⊢ Ind (SU.SInd.name ind) ≡ T′ ^ [ ! , ι ⁰ ]) (PE.sym emb≡Ind)
                                (refl (univ (Indⱼ ⊢Δ)))
        in  consⱼ (conv ⊢a ⊢Ind≡emb) (to⊢All [Δ] poss ps (PE.cong pred eq))
      to⊢All {args = []} {Ts = _ List∷ _} [Δ] _ []ₐ ()
      to⊢All {args = _ List∷ _} {Ts = []} [Δ] []ₐ _ ()

      go : ∀ {args args'}
         → All₂ (λ a a' → Γ ⊢ a ≡ a' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]) args args'
         → Σ (⊩ᵛ Γ) (λ [Γ] →
              All (λ a → Γ ⊩ᵛ⟨ ∞ ⟩ a ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Γ]) args
              × All (λ a' → Γ ⊩ᵛ⟨ ∞ ⟩ a' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Γ]) args'
              × All₂ (λ a a' → Γ ⊩ᵛ⟨ ∞ ⟩ a ≡ a' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Γ]) args args')
      go []ₐ = valid ⊢Γ , []ₐ , []ₐ , []ₐ
      go {args = a List∷ as} {args' = a' List∷ as'} (eq ∷ₐ eqs)
        with fundamentalTermEq eq | go eqs
      ... | [Γ₁] , modelsTermEq [Ind₁] [a]ₜ [a']ₜ [a≡a']
          | [Γ₂] , [as]ᵥ , [as']ᵥ , [as≡]ᵥ =
        let [Γ]′ = [Γ₂]
            [Ind]′ = Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Γ]′
            [a]″ = S.irrelevanceTerm {A = Ind (SU.SInd.name ind)} {t = a} [Γ₁] [Γ]′ [Ind₁] [Ind]′ [a]ₜ
            [a']″ = S.irrelevanceTerm {A = Ind (SU.SInd.name ind)} {t = a'} [Γ₁] [Γ]′ [Ind₁] [Ind]′ [a']ₜ
            [a≡a']″ = S.irrelevanceEqTerm {A = Ind (SU.SInd.name ind)} {t = a} {u = a'}
                                         [Γ₁] [Γ]′ [Ind₁] [Ind]′ [a≡a']
        in  [Γ]′ , [a]″ ∷ₐ [as]ᵥ , [a']″ ∷ₐ [as']ᵥ , [a≡a']″ ∷ₐ [as≡]ᵥ

  fundamentalTermEq {Γ} (IndRect-cong {ind} {P} {P'} {lG} {t} {t'} {ms} {ms'} ind∈ P≡P' t≡t' ⊢ms≡)
    with fundamentalEq P≡P' | fundamentalTermEq t≡t'
  ... | [ΓP] , [P] , [P'] , [P≡P']
      | [Γt] , modelsTermEq [Indt] [t] [t'] [t≡t'] =
    let i = (SU.SInd.name ind)
        [Γ]′ = [Γt]
        [Ind] = Indᵛ {i = i} {l = ∞} [Γ]′
        [Ind≡Ind] = reflᵛ {A = Ind i} [Γ]′ [Ind]
        [Γ∙Ind] = _∙_ {A = Ind i} [Γ]′ [Ind]
        [P]′ = S.irrelevance {A = P} [ΓP] [Γ∙Ind] [P]
        [P']′ = S.irrelevance {A = P'} [ΓP] [Γ∙Ind] [P']
        [P≡P']′ = S.irrelevanceEq {A = P} {B = P'} [ΓP] [Γ∙Ind] [P] [P]′ [P≡P']
        [t]′ = S.irrelevanceTerm {A = Ind i} {t = t} [Γt] [Γ]′ [Indt] [Ind] [t]
        [t']′ = S.irrelevanceTerm {A = Ind i} {t = t'} [Γt] [Γ]′ [Indt] [Ind] [t']
        [t≡t']′ = S.irrelevanceEqTerm {A = Ind i} {t = t} {u = t'} [Γt] [Γ]′ [Indt] [Ind] [t≡t']
        [Pt] = substS {F = Ind i} {G = P} {t = t} [Γ]′ [Ind] [P]′ [t]′
        [P't'] = substS {F = Ind i} {G = P'} {t = t'} [Γ]′ [Ind] [P']′ [t']′
        [Pt≡P't'] = substSEq {Ind i} {Ind i} {P} {P'} {t} {t'}
                             [Γ]′ [Ind] [Ind] [Ind≡Ind] [P]′ [P']′ [P≡P']′
                             [t]′ [t']′ [t≡t']′
        ⊢ms = msLeft ⊢ms≡
        ⊢ms' = msRight ⊢ms≡
        [ms] = fundamentalAllMethods {ind = ind} {P = P} {rG = !} {lG = lG} {ms = ms} [Γ]′ ⊢ms
        -- ⊢ms' is under P (Typed IndRect-cong); transport it to P' for the RHS.
        ⊢ms'P' = msRight (indRectBranchTyListCong ind∈ P≡P'
                            (λ d ⊢Δ [σ] ⊢u → subTypeEq ⊢Δ ([σ] , ⊢u) P≡P') ⊢ms≡)
        [ms'] = fundamentalAllMethods {ind = ind} {P = P'} {rG = !} {lG = lG} {ms = ms'} [Γ]′ ⊢ms'P'
    in  [Γ]′
    ,   modelsTermEq [Pt]
                     (IndRectᵛ {ind = ind} {P = P} {rG = !} {lG = lG} {t = t} {ms = ms} {l = ∞}
                               (λ abs → ⊥-elim (!≢% abs)) [Γ]′ ind∈ [Ind] [P]′ [t]′ [Pt] ⊢ms [ms])
                     (conv₂ᵛ {IndRect i lG P' t' ms'} {P [ t ]} {P' [ t' ]}
                             [Γ]′ [Pt] [P't'] [Pt≡P't']
                             (IndRectᵛ {ind = ind} {P = P'} {rG = !} {lG = lG} {t = t'} {ms = ms'} {l = ∞}
                                       (λ abs → ⊥-elim (!≢% abs)) [Γ]′ ind∈ [Ind] [P']′ [t']′ [P't'] ⊢ms'P' [ms']))
                     (IndRect-congᵛ {ind = ind} {P = P} {P' = P'} {lG = lG} {t = t} {t' = t'} {ms = ms} {ms' = ms'}
                                    (λ abs → ⊥-elim (!≢% abs)) [Γ]′ [Ind] [P]′ [P']′ [P≡P']′
                                    [t]′ [t']′ [t≡t']′ [Pt] ⊢ms ⊢ms' ⊢ms≡ PE.refl)
    where
      msLeft : ∀ {ts ts' As r} → Γ ⊢All ts ≡ ts' ∷ As ^ r → Γ ⊢All ts ∷ As ^ r
      msLeft εⱼ = εⱼ
      msLeft (consⱼ eq rest) with fundamentalTermEq eq
      ... | [Γe] , modelsTermEq [A] [t] [_u] _ =
        consⱼ (escapeTermᵛ [Γe] [A] [t]) (msLeft rest)

      msRight : ∀ {ts ts' As r} → Γ ⊢All ts ≡ ts' ∷ As ^ r → Γ ⊢All ts' ∷ As ^ r
      msRight εⱼ = εⱼ
      msRight (consⱼ eq rest) with fundamentalTermEq eq
      ... | [Γe] , modelsTermEq [A] [_t] [u] _ =
        consⱼ (escapeTermᵛ [Γe] [A] [u]) (msRight rest)

  fundamentalTermEq {Γ} (IndRect-ctr≡ {ind} {j} {P} {lG} {args} {ms} {m} {Ts} ind∈ eq ⊢P ⊢args ⊢ms nth≡)
    with fundamental ⊢P
  ... | [Γ] ∙ [Ind₀] , [P] =
    let i = (SU.SInd.name ind)
        [Ind] = Indᵛ {i = i} {l = ∞} [Γ]
        [Γ∙Ind] = _∙_ {A = Ind i} [Γ] [Ind]
        [P]′ = S.irrelevance {A = P} ([Γ] ∙ [Ind₀]) [Γ∙Ind] [P]
        [args]ᵥ = fundamentalAllInd {ind = ind} {j = j} {Ts = Ts} {args = args} [Γ] [Ind] eq ⊢args
        [d] = ctrᵛ {ind = ind} {j = j} {args = args} {Ts = Ts} {l = ∞} [Γ] [Ind] ind∈ eq ⊢args [args]ᵥ
        [Pd] = substS {F = Ind i} {G = P} {t = ctr i j args} [Γ] [Ind] [P]′ [d]
        rhs = apps lG m
                     (args ++ map (λ a → IndRect i lG P a ms) args)
        [ms]ᵥ = fundamentalAllMethods {ind = ind} {P = P} {rG = !} {lG = lG} {ms = ms} [Γ] ⊢ms
        [rhs] = IndRect-ctr-rhsᵛ {ind = ind} {j = j} {P = P} {lG = lG}
                                 {args = args} {ms = ms} {Ts = Ts} {l = ∞}
                                 [Γ] ind∈ [Ind] [P]′ [args]ᵥ [Pd] eq ⊢args ⊢ms [ms]ᵥ nth≡
        [lhs] , [redEq] =
          redSubstTermᵛ {A = P [ ctr i j args ]}
                        {t = IndRect i lG P (ctr i j args) ms}
                        {u = rhs} [Γ]
            (λ {Δ} {σ} ⊢Δ [σ] →
               let ⊢Indσ = escape (proj₁ ([Ind] ⊢Δ [σ]))
                   ⊢Pσ = escape (proj₁ ([P]′ (⊢Δ ∙ ⊢Indσ)
                                             (liftSubstS {F = Ind i} [Γ] ⊢Δ [Ind] [σ])))
                   ⊢argsσ = substAll-ctrArgs {σ = σ} [Γ] ⊢Δ [σ] ⊢args
                   ⊢msσ = substAll-indRectBranch {σ = σ} {ind = ind} {P = P} [Γ] ⊢Δ [σ] ⊢ms
                   step = IndRect-ctr ind∈ eq ⊢Pσ ⊢argsσ ⊢msσ (nth-map (subst σ) ms j nth≡)
                   lhs≡ = PE.trans (subst-IndRect σ i lG P (ctr i j args) ms)
                                   (PE.cong (λ t′ → IndRect i lG (subst (liftSubst σ) P) t′
                                                      (map (subst σ) ms))
                                            (subst-ctr σ i j args))
                   rhs≡ = subst-IndRect-ctr-rhs σ i lG P m args ms
                   ty≡  = PE.trans (singleSubstLift P (ctr i j args))
                                   (PE.cong (λ t′ → subst (liftSubst σ) P [ t′ ])
                                            (subst-ctr σ i j args))
               in  PE.subst₃ (λ t′ u′ A′ → Δ ⊢ t′ ⇒ u′ ∷ A′ ^ ι lG)
                             (PE.sym lhs≡) (PE.sym rhs≡) (PE.sym ty≡) step)
                        [Pd] [rhs]
    in  [Γ] , modelsTermEq [Pd] [lhs] [rhs] [redEq]
  fundamentalTermEq (natrec-cong {z} {z′} {s} {s′} {n} {n′} {F} {F′}
                                 F≡F′ z≡z′ s≡s′ n≡n′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq z≡z′      |
         fundamentalTermEq s≡s′      |
         fundamentalTermEq n≡n′
  fundamentalTermEq (natrec-cong {z} {z′} {s} {s′} {n} {n′} {F} {F′} {l}
                                 F≡F′ z≡z′ s≡s′ n≡n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]₁ , modelsTermEq [F₀] [z] [z′] [z≡z′] |
    [Γ]₂ , modelsTermEq [F₊] [s] [s′] [s≡s′] |
    [Γ]₃ , modelsTermEq [ℕ] [n] [n′] [n≡n′] =
      let sType = Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var 0) ]↑ ° l ° l ^ !) ° l ° l ^ !
          s′Type = Π ℕ ^ ! ° ⁰ ▹ (F′ ^ ! ° l ▹▹ F′ [ suc (var 0) ]↑ ° l ° l ^ !) ° l ° l ^ !
          [0] = S.irrelevanceTerm {l = ∞} {A = ℕ} {t = zero}
                                  [Γ]₃ [Γ]₃ (ℕᵛ [Γ]₃) [ℕ] (zeroᵛ {l = ∞} [Γ]₃)
          [F]′ = S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ [ℕ]) [F]
          [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₁ [Γ]₃ [F₀]
          [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]₃ [F₊]
          [Fₙ]′ = substS {ℕ} {F} {n} [Γ]₃ [ℕ] [F]′ [n]
          [F′]′ = S.irrelevance {A = F′} [Γ] ([Γ]₃ ∙ [ℕ]) [F′]
          [F₀]″ = substS {ℕ} {F} {zero} [Γ]₃ [ℕ] [F]′ [0]
          [F′₀]′ = substS {ℕ} {F′} {zero} [Γ]₃ [ℕ] [F′]′ [0]
          [F′₊]′ = sucCase {F′} (λ abs → ⊥-elim (!≢% abs)) [Γ]₃ [ℕ] [F′]′
          [F′ₙ′]′ = substS {ℕ} {F′} {n′} [Γ]₃ [ℕ] [F′]′ [n′]
          [ℕ≡ℕ] = reflᵛ {ℕ} [Γ]₃ [ℕ]
          [0≡0] = reflᵗᵛ {ℕ} {zero} [Γ]₃ [ℕ] [0]
          [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′}
                                    [Γ] ([Γ]₃ ∙ [ℕ]) [F] [F]′ [F≡F′]
          [F₀≡F′₀] = substSEq {ℕ} {ℕ} {F} {F′} {zero} {zero}
                              [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ]
                              [F]′ [F′]′ [F≡F′]′ [0] [0] [0≡0]
          [F₀≡F′₀]′ = S.irrelevanceEq {A = F [ zero ]} {B = F′ [ zero ]}
                                      [Γ]₃ [Γ]₃ [F₀]″ [F₀]′ [F₀≡F′₀]
          [F₊≡F′₊] = sucCaseCong {F} {F′} (λ abs → ⊥-elim (!≢% abs)) [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
          [F₊≡F′₊]′ = S.irrelevanceEq {A = sType} {B = s′Type}
                                      [Γ]₃ [Γ]₃ (sucCase {F} (λ abs → ⊥-elim (!≢% abs)) [Γ]₃ [ℕ] [F]′)
                                      [F₊]′ [F₊≡F′₊]
          [Fₙ≡F′ₙ′]′ = substSEq {ℕ} {ℕ} {F} {F′} {n} {n′}
                                [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ] [F]′ [F′]′ [F≡F′]′
                                [n] [n′] [n≡n′]
          [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                   [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z]
          [z′]′ = convᵛ {z′} {F [ zero ]} {F′ [ zero ]}
                        [Γ]₃ [F₀]′ [F′₀]′ [F₀≡F′₀]′
                        (S.irrelevanceTerm {A = F [ zero ]} {t = z′}
                                           [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z′])
          [z≡z′]′ = S.irrelevanceEqTerm {A = F [ zero ]} {t = z} {u = z′}
                                        [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z≡z′]
          [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s]
          [s′]′ = convᵛ {s′} {sType} {s′Type} [Γ]₃ [F₊]′ [F′₊]′ [F₊≡F′₊]′
                        (S.irrelevanceTerm {A = sType} {t = s′}
                                           [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s′])
          [s≡s′]′ = S.irrelevanceEqTerm {A = sType} {t = s} {u = s′}
                                        [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s≡s′]
      in  [Γ]₃
      ,   modelsTermEq [Fₙ]′
                       (natrecᵛ {F} { ! } {l} {z} {s} {n} (λ abs → ⊥-elim (!≢% abs))
                                [Γ]₃ [ℕ] [F]′ [F₀]′ [F₊]′ [Fₙ]′ [z]′ [s]′ [n])
                       (conv₂ᵛ {natrec l F′ z′ s′ n′} {F [ n ]} {F′ [ n′ ]}
                               [Γ]₃ [Fₙ]′ [F′ₙ′]′ [Fₙ≡F′ₙ′]′
                               (natrecᵛ {F′} { ! } {l} {z′} {s′} {n′} (λ abs → ⊥-elim (!≢% abs))
                                        [Γ]₃ [ℕ] [F′]′ [F′₀]′ [F′₊]′ [F′ₙ′]′
                                        [z′]′ [s′]′ [n′]))
                       (natrec-congᵛ {F} {F′} { ! } {l} {z} {z′} {s} {s′} {n} {n′} (λ abs → ⊥-elim (!≢% abs))
                                     [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
                                     [F₀]′ [F′₀]′ [F₀≡F′₀]′
                                     [F₊]′ [F′₊]′ [F₊≡F′₊]′ [Fₙ]′
                                     [z]′ [z′]′ [z≡z′]′
                                     [s]′ [s′]′ [s≡s′]′ [n] [n′] [n≡n′]) 
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s)
    with fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  fundamentalTermEq (natrec-zero {z} {s} {F} {l} ⊢F ⊢z ⊢s) | [Γ] , [F]
    | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [F₊] , [s] =
    let sType = Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var 0) ]↑ ° l ° l ^ !) ° l ° l ^ !
        [Γ]′ = [Γ]₁
        [ℕ]′ = ℕᵛ {l = ∞} [Γ]′
        [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]′ [F₊]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]′ [F₊] [F₊]′ [s]
        [F]′ = S.irrelevance {A = F} [Γ] ([Γ]′ ∙ [ℕ]′) [F]
        d , r =
          redSubstTermᵛ {F [ zero ]} {natrec l F z s zero} {z} [Γ]′
            (λ {Δ} {σ} ⊢Δ [σ] →
               let ⊢ℕ = escape (proj₁ ([ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ ([F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]′ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x ^ _)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                (proj₁ ([z] ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι l ] )
                                 (natrecSucCase σ F ! l)
                                 (escapeTerm (proj₁ ([F₊]′ ⊢Δ [σ]))
                                                (proj₁ ([s]′ ⊢Δ [σ])))
               in PE.subst (λ x → Δ ⊢ subst σ (natrec l F z s zero)
                                    ⇒ subst σ z ∷ x ^ _)
                           (PE.sym (singleSubstLift F zero))
                           (natrec-zero ⊢F ⊢z ⊢s))
                        [F₀] [z]
    in  [Γ]′ , modelsTermEq [F₀] d [z] r
  fundamentalTermEq (natrec-suc {n} {z} {s} {F} {lF} ⊢n ⊢F ⊢z ⊢s)
    with fundamentalTerm ⊢n | fundamental ⊢F
       | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [ℕ]′ = S.irrelevance {A = ℕ} [Γ] [Γ]₃ [ℕ]
        [n]′ = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]₃ [ℕ] [ℕ]′ [n]
        [sucn] = sucᵛ {n = n} [Γ]₃ [ℕ]′ [n]′
        [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₂ [Γ]₃ [F₀]
        [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                 [Γ]₂ [Γ]₃ [F₀] [F₀]′ [z]
        [F]′ = S.irrelevance {A = F} [Γ]₁ ([Γ]₃ ∙ [ℕ]′) [F]
        [F[sucn]] = substS {ℕ} {F} {suc n} [Γ]₃ [ℕ]′ [F]′ [sucn]
        [Fₙ]′ = substS {ℕ} {F} {n} [Γ]₃ [ℕ]′ [F]′ [n]′
        [F+n] = substSΠ {ℕ} {F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !} {n} [Γ]₃ [ℕ]′ [F₊] [n]′ 
        [natrecₙ] = natrecᵛ {F} { ! } {lF} {z} {s} {n} (λ abs → ⊥-elim (!≢% abs))
                            [Γ]₃ [ℕ]′ [F]′ [F₀]′ [F₊] [Fₙ]′ [z]′ [s] [n]′
        t = (s ∘ n ^ lF) ∘ (natrec lF F z s n) ^ lF
        q = subst (liftSubst (sgSubst n))
                  (wk1 (F [ suc (var 0) ]↑))
        y = S.irrelevanceTerm′
              {A = q [ natrec lF F z s n ]} {A′ = F [ suc n ]} {t = t}
              (natrecIrrelevantSubst′ F z s n) PE.refl [Γ]₃ [Γ]₃
              (substSΠ {F [ n ]} {q} {natrec lF F z s n} [Γ]₃
                [Fₙ]′
                [F+n]
                [natrecₙ])
              [F[sucn]]
              (appᵛ {F [ n ]} {q} { ! } {lF} {lF} {lF} {s ∘ n ^ lF} {natrec lF F z s n} [Γ]₃ [Fₙ]′ (decompΠᵛ {F = F [ n ]} {G = q} [Γ]₃ [Fₙ]′ [F+n])
                (substSΠ {ℕ} {F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !} {n}
                         [Γ]₃ [ℕ]′ [F₊] [n]′)
                (appᵛ {ℕ} {F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !} { ! } {⁰} {lF} {lF} {s} {n}
                      [Γ]₃ [ℕ]′ (decompΠᵛ {F = ℕ} {G = F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !} [Γ]₃ [ℕ]′ [F₊]) [F₊] [s] [n]′)
                [natrecₙ])
        d , r =
          redSubstTermᵛ {F [ suc n ]} {natrec lF F z s (suc n)} {t } {∞} {_} [Γ]₃
            (λ {Δ} {σ} ⊢Δ [σ] →
               let ⊢n = escapeTerm (proj₁ ([ℕ]′ ⊢Δ [σ]))
                                      (proj₁ ([n]′ ⊢Δ [σ]))
                   ⊢ℕ = escape (proj₁ ([ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ ([F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]₃ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x ^ _)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ ([F₀]′ ⊢Δ [σ]))
                                                (proj₁ ([z]′ ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ])
                                 (natrecSucCase σ F ! lF)
                                 (escapeTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                (proj₁ ([s] ⊢Δ [σ])))
                   r = _⊢_⇒_∷_^_.natrec-suc {n = subst σ n}
                                          {z = subst σ z} {s = subst σ s}
                                          {F = subst (liftSubst σ) F}
                                          ⊢n ⊢F ⊢z ⊢s 
               in PE.subst (λ x → Δ ⊢ subst σ (natrec lF F z s (suc n))
                                    ⇒ (subst σ t) ∷ x ^ _)
                           (PE.trans (PE.trans (substCompEq F)
                             (substVar-to-subst (λ { 0 → PE.refl
                                         ; (1+ x) → PE.trans (subst-wk (σ x))
                                                              (subst-id (σ x))
                                         })
                                      F))
                             (PE.sym (substCompEq F)))
                           r)
                        [F[sucn]] y
    in  [Γ]₃ , modelsTermEq [F[sucn]] d y r
  fundamentalTermEq (Emptyrec-cong {F} {F′} {n} {n′}
                                 F≡F′ ⊢n ⊢n′)
    with fundamentalEq F≡F′ | fundamentalTerm ⊢n | fundamentalTerm ⊢n′
  fundamentalTermEq (Emptyrec-cong {F} {F′} {lF} {n} {n′}
                                 F≡F′ ⊢n ⊢n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γn]  , [Empty] ,  [n] | [Γn′] , [Empty]′ , [n′]
    =
    let [F]′ = S.irrelevance {A = F} [Γ] [Γn′] [F]
        [F′]′ = S.irrelevance {A = F′} [Γ] [Γn′] [F′]
        [n]′ = S.irrelevanceTerm {A = Empty _} {t = n} [Γn] [Γn′] [Empty] [Empty]′ [n]
        [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} [Γ] [Γn′] [F] [F]′ [F≡F′]
    in [Γn′]
      , modelsTermEq [F]′ (Emptyrecᵛ {F} { ! } {lF} {n} [Γn′] [Empty]′ [F]′ [n]′)
                     (conv₂ᵛ {Emptyrec lF ⁰ F′ n′} {F} {F′} { [ ! , ι lF ] } [Γn′] [F]′ [F′]′ [F≡F′]′
                       (Emptyrecᵛ {F′} { ! } {lF} {n′} [Γn′] [Empty]′ [F′]′ [n′]))
                     (Emptyrec-congᵛ {F} {F′} { ! } {lF} {n} {n′}
                        [Γn′] [Empty]′ [F]′ [F′]′ [F≡F′]′ [n]′ [n′])
  fundamentalTermEq (proof-irrelevance ⊢t ⊢u) with fundamentalTerm ⊢t | fundamentalTerm ⊢u
  fundamentalTermEq {A = A} {t = t} {t′ = t′} (proof-irrelevance ⊢t ⊢u) | [Γ] , [A] , [t] | [Γ]′ , [A]′ , [u] =
    let [u]′ = S.irrelevanceTerm {A = A} {t = t′} [Γ]′ [Γ] [A]′ [A] [u]
    in [Γ] , modelsTermEq [A] [t] [u]′
                           (PI.proof-irrelevanceᵛ {A = A} {t = t} {u = t′} [Γ] [A] [t] [u]′)

  fundamentalTermEq (Id-cong {A} {A'} {l} {t} {t'} {u} {u'} A≡A' t≡t' u≡u') 
    with fundamentalTermEq A≡A' | fundamentalTermEq t≡t' | fundamentalTermEq u≡u'
  ... | [ΓA] , modelsTermEq [UA] [A]ₜ [A']ₜ [A≡A']ₜ | [Γt] , modelsTermEq [A] [t]ₜ [t']ₜ [t≡t']ₜ  | [Γu] , modelsTermEq [A'] [u]ₜ [u']ₜ [u≡u']ₜ =
    let [SProp] = maybeEmbᵛ {A = Univ _ _} [Γu] (Uᵛ {rU = %} <next [Γu]) 
        [UA]′ = maybeEmbᵛ {A = U l} [Γu] (Uᵛ <next [Γu])
        [A]ₜ′ = S.irrelevanceTerm {A = U l} {t = A} [ΓA] [Γu] [UA] (λ {Δ} {σ} → [UA]′ {Δ} {σ}) [A]ₜ
        [A']ₜ′ = S.irrelevanceTerm {A = U l} {t = A'} [ΓA] [Γu] [UA] [UA]′ [A']ₜ
        [A]′ = S.irrelevance {A = A} [Γt] [Γu] [A]
        [A']ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A'} [ΓA] [Γu] [UA] [UA]′ [A']ₜ
        [A']′ = maybeEmbᵛ {A = A'} [Γu] (univᵛ {A = A'} [Γu] (≡is≤ PE.refl) [UA]′ [A']ₜ′)
        [A≡A']ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = A} {u = A'} [ΓA] [Γu] [UA] [UA]′ [A≡A']ₜ
        [A≡A']′ = univEqᵛ {A = A} {B = A'} [Γu] [UA]′ [A]′ [A≡A']ₜ′
        [t]ₜ′ = S.irrelevanceTerm {A = A} {t = t} [Γt] [Γu] [A] [A]′ [t]ₜ
        [t']ₜ′ = convᵛ {t = t'} {A = A} {B = A'} [Γu] [A]′ [A']′ [A≡A']′ (S.irrelevanceTerm {A = A} {t = t'} [Γt] [Γu] [A] [A]′ [t']ₜ)
        [u]ₜ′ = S.irrelevanceTerm {A = A} {t = u} [Γu] [Γu] [A'] [A]′ [u]ₜ
        [u']ₜ′ = convᵛ {t = u'} {A = A} {B = A'} [Γu] [A]′ [A']′ [A≡A']′ (S.irrelevanceTerm {A = A} {t = u'} [Γu] [Γu] [A'] [A]′ [u']ₜ)
        [t≡t']ₜ′ = S.irrelevanceEqTerm {A = A} {t = t} {u = t'} [Γt] [Γu] [A] [A]′ [t≡t']ₜ
        [u≡u']ₜ′ = S.irrelevanceEqTerm {A = A} {t = u} {u = u'} [Γu] [Γu] [A'] [A]′ [u≡u']ₜ
    in [Γu] , modelsTermEq [SProp] (Idᵗᵛ {A} {t} {u} [Γu] [A]′ [t]ₜ′ [u]ₜ′ [A]ₜ′)
                                   (Idᵗᵛ {A'} {t'} {u'} [Γu] [A']′ [t']ₜ′ [u']ₜ′ [A']ₜ′)
                                   (Id-congᵗᵛ {A} {A'} {t} {t'} {u} {u'} [Γu] [A]′ [t]ₜ′ [u]ₜ′ [A]ₜ′ [A']′ [t']ₜ′ [u']ₜ′ [A']ₜ′ [A≡A']ₜ′ [t≡t']ₜ′ [u≡u']ₜ′)

{-
  fundamentalTermEq {Γ} (Id-Π {A} {rA} {lA} {lB} {l} {B} {t} {u} lA≤ lB≤ ⊢A ⊢B ⊢t ⊢u) 
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  ... | [ΓA] , [UA] , [A]ₜ  | [ΓB] ∙ [AB] , [UB] , [B]ₜ | [Γt] , [Πt] , [t]ₜ | [Γu] , [Πu] , [u]ₜ =
    let [SProp] = maybeEmbᵛ {A = Univ _ _} [Γu] (Uᵛ {rU = %} (proj₂ (levelBounded l)) [Γu]) 
        [UA]′ =  maybeEmbᵛ {A = Univ _ _} [Γu] (Uᵛ (proj₂ (levelBounded lA)) [Γu])
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [Γu] [UA] [UA]′ [A]ₜ
        [A] = maybeEmbᵛ {A = A} [Γu] (univᵛ {A = A} [Γu] (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [ΓuA] = _∙_ {A = A} [Γu] [A]
        [UB]′  = S.irrelevance {A = Univ _ _} (_∙_ {A = A} [ΓB] [AB]) (_∙_ {A = A} [Γu] [A]) (λ {Δ} {σ} → [UB] {Δ} {σ})
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} (_∙_ {A = A} [ΓB] [AB]) [ΓuA] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [t]ₜ′  = S.irrelevanceTerm {A = Π A ^ rA ° lA ▹ B ° lB ° l ^ !} {t = t} [Γt] [Γu] [Πt] [Πu] [t]ₜ
    in  [Γu] , Id-Πᵗᵛ [Γu] lA≤ lB≤ [A] (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [A]ₜ′ [B]ₜ′ [Πu] [t]ₜ′ [u]ₜ
-}

  fundamentalTermEq (cast-refl {A} {B} {e} {t} A≡B ⊢e ⊢t)
    with fundamentalTermEq A≡B | fundamentalTerm ⊢e | fundamentalTerm ⊢t 
  ... | [Γ] , modelsTermEq [UA] [A]ₜ [B]ₜ [A≡B]ₜ
      | [Γe] , [IdAB] , [e]ₜ | [Γt] , [A]₁ , [t]ₜ  = 
    let [A] = maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ)
        [B] = maybeEmbᵛ {A = B} [Γ] (univᵛ {A = B} [Γ] (≡is≤ PE.refl) [UA] [B]ₜ)
        [UA]′  = S.irrelevance {A = Univ _ _} [Γ] [Γt] [UA]
        [A]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γt] [UA] [UA]′ [A]ₜ
        [B]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = B} [Γ] [Γt] [UA] [UA]′ [B]ₜ
        [A]′ = maybeEmbᵛ {A = A} [Γt] (univᵛ {A = A} [Γt] (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [t]ₜ′ = S.irrelevanceTerm {A = A} {t = t} [Γt] [Γt] [A]₁ [A]′ [t]ₜ
        [A≡B]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = A} {u = B} [Γ] [Γt] [UA] [UA]′ [A≡B]ₜ
        [A≡B]′ = S.irrelevanceEq {A = A} {B = B} [Γ] [Γt] [A] [A]′ (univEqᵛ {A = A} {B = B} [Γ] [UA] [A] [A≡B]ₜ)
        [B]′ = maybeEmbᵛ {A = B} [Γt] (univᵛ {A = B} [Γt] (≡is≤ PE.refl) [UA]′ [B]ₜ′)
        [IdAB]′  = S.irrelevance {A = Id (Univ _ _) A B} [Γe] [Γt] [IdAB]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _) A B} {t = e} [Γe] [Γt] [IdAB] [IdAB]′ [e]ₜ
    in  [Γt]
    ,   modelsTermEq [B]′ (castᵗᵛ {A} {B} { ! } {t} {e} [Γt] [UA]′ [A]ₜ′ [B]ₜ′ [A]′ [B]′ [t]ₜ′ [IdAB]′ [e]ₜ′)
                          (convᵛ {t} {A} {B} [Γt] [A]′ [B]′ [A≡B]′ [t]ₜ′)
                          (cast-reflᵗᵛ {A} {B} {e} {t} [Γt] [UA]′ [A]ₜ′ [B]ₜ′ [A≡B]ₜ′ [A]′ [B]′ [t]ₜ′ [IdAB]′ [e]ₜ′)

  fundamentalTermEq (cast-cong {A} {A'} {B} {B'} {e} {e'} {t} {t'} A≡A' B≡B' t≡t' ⊢e ⊢e')
    with fundamentalTermEq A≡A' | fundamentalTermEq B≡B' | fundamentalTermEq t≡t' | fundamentalTerm ⊢e | fundamentalTerm ⊢e'
  ... | [Γ] , modelsTermEq [UA] [A]ₜ [A']ₜ [A≡A']ₜ | [Γ]₁ , modelsTermEq [UB] [B]ₜ [B']ₜ [B≡B']ₜ
      | [Γ]₂ , modelsTermEq [A]₁ [t]ₜ [t']ₜ [t≡t']ₜ | [Γe] , [IdAB] , [e]ₜ
      | [Γe'] , [IdAB'] , [e']ₜ = 
    let [A] = maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ)
        [B] = maybeEmbᵛ {A = B} [Γ]₁ (univᵛ {A = B} [Γ]₁ (≡is≤ PE.refl) [UB] [B]ₜ)
        [UA]′  = S.irrelevance {A = Univ _ _} [Γ] [Γ]₂ [UA]
        [A]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]₂ [UA] [UA]′ [A]ₜ
        [A']ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A'} [Γ] [Γ]₂ [UA] [UA]′ [A']ₜ
        [UB]′  = S.irrelevance {A = Univ _ _} [Γ]₁ [Γ]₂ [UB]
        [B]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = B} [Γ]₁ [Γ]₂ [UB] [UB]′ [B]ₜ
        [B]ₜ′′ = S.irrelevanceTerm {A = Univ _ _} {t = B} [Γ]₁ [Γ]₂ [UB] [UA]′ [B]ₜ
        [B']ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = B'} [Γ]₁ [Γ]₂ [UB] [UB]′ [B']ₜ
        [B']ₜ′′ = S.irrelevanceTerm {A = Univ _ _} {t = B'} [Γ]₁ [Γ]₂ [UB] [UA]′ [B']ₜ
        [A]′ = maybeEmbᵛ {A = A} [Γ]₂ (univᵛ {A = A} [Γ]₂ (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [t]ₜ′ = S.irrelevanceTerm {A = A} {t = t} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t]ₜ
        [A']′ = maybeEmbᵛ {A = A'} [Γ]₂ (univᵛ {A = A'} [Γ]₂ (≡is≤ PE.refl) [UA]′ [A']ₜ′)
        [t']ₜ′ = S.irrelevanceTerm {A = A} {t = t'} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t']ₜ
        [A≡A']ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = A} {u = A'} [Γ] [Γ]₂ [UA] [UA]′ [A≡A']ₜ
        [A≡A']′ = S.irrelevanceEq {A = A} {B = A'} [Γ] [Γ]₂ [A] [A]′ (univEqᵛ {A = A} {B = A'} [Γ] [UA] [A] [A≡A']ₜ)
        [t'A]ₜ = convᵛ {t'} {A} {A'} [Γ]₂ [A]′ [A']′ [A≡A']′ [t']ₜ′
        [t≡t']ₜ′ = S.irrelevanceEqTerm {A = A} {t = t} {u = t'} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t≡t']ₜ
        [B]′ = maybeEmbᵛ {A = B} [Γ]₂ (univᵛ {A = B} [Γ]₂ (≡is≤ PE.refl) [UB]′ [B]ₜ′)
        [B']′ = maybeEmbᵛ {A = B'} [Γ]₂ (univᵛ {A = B'} [Γ]₂ (≡is≤ PE.refl) [UB]′ [B']ₜ′)
        [B≡B']ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = B} {u = B'} [Γ]₁ [Γ]₂ [UB] [UB]′ [B≡B']ₜ
        [B≡B']′ = S.irrelevanceEq {A = B} {B = B'} [Γ]₁ [Γ]₂ [B] [B]′ (univEqᵛ {A = B} {B = B'} [Γ]₁ [UB] [B] [B≡B']ₜ)
        [IdAB]′  = S.irrelevance {A = Id (Univ _ _) A B} [Γe] [Γ]₂ [IdAB]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _) A B} {t = e} [Γe] [Γ]₂ [IdAB] [IdAB]′ [e]ₜ
        [IdAB']′  = S.irrelevance {A = Id (Univ _ _) A' B'} [Γe'] [Γ]₂ [IdAB']
        [e']ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _) A' B'} {t = e'} [Γe'] [Γ]₂ [IdAB'] [IdAB']′ [e']ₜ
    in  [Γ]₂
    ,   modelsTermEq [B]′ (castᵗᵛ {A} {B} { ! } {t} {e} [Γ]₂ [UA]′ [A]ₜ′ [B]ₜ′′ [A]′ [B]′ [t]ₜ′ [IdAB]′ [e]ₜ′)
                          (conv₂ᵛ {cast _ A' B' e' t'} {B} {B'} [Γ]₂ [B]′ [B']′ [B≡B']′
                            (castᵗᵛ {A'} {B'} { ! } {t'} {e'} [Γ]₂ [UA]′ [A']ₜ′ [B']ₜ′′ [A']′ [B']′ [t'A]ₜ [IdAB']′ [e']ₜ′))
                          (cast-congᵗᵛ {A} {A'} {B} {B'} {t} {t'} {e} {e'} [Γ]₂ [UA]′ [UB]′ [A]ₜ′ [A']ₜ′ [B]ₜ′ [B']ₜ′ [A≡A']ₜ′ [B≡B']ₜ′ [A]′ [A']′ [B]′ [B']′ [t]ₜ′ [t'A]ₜ [t≡t']ₜ′
                                       [IdAB]′ [e]ₜ′ [IdAB']′ [e']ₜ′)

  fundamentalTermEq (cast-ℕ-0 {e} ⊢e) with fundamentalTerm ⊢e
  ... | [Γ] , [Id] , [e]ₜ =
    let ⊢eΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([Id] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e]ₜ {Δ} {σ} ⊢Δ [σ]))
        [zero] = zeroᵛ {l = ∞} [Γ]
        [id] , [eq] = redSubstTermᵛ {ℕ} {cast ⁰ ℕ ℕ e zero} {zero} {∞} [Γ]
                                    (λ {Δ} {σ} ⊢Δ [σ] → cast-ℕ-0 (⊢eΔ {Δ} {σ} ⊢Δ [σ]))
                                    (ℕᵛ [Γ]) [zero]
    in [Γ] , modelsTermEq (ℕᵛ [Γ]) [id] [zero] [eq] 
  fundamentalTermEq (cast-ℕ-S {e} {n} ⊢e ⊢n) with fundamentalTerm ⊢e | fundamentalTerm ⊢n 
  ... | [Γ] , [Id] , [e]ₜ | [Γ]₁ , [ℕ] , [n]ₜ =
    let [Id]′  = S.irrelevance {A = Id (U _) ℕ ℕ} [Γ] [Γ]₁ [Id]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (U _) ℕ ℕ} {t = e} [Γ] [Γ]₁ [Id] [Id]′ [e]ₜ
        ⊢eΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([Id]′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e]ₜ′ {Δ} {σ} ⊢Δ [σ]))
        ⊢nΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([n]ₜ {Δ} {σ} ⊢Δ [σ]))
        [suc-cast] = sucᵛ {n = cast ⁰ ℕ ℕ e n} [Γ]₁ [ℕ] (castᵗᵛ {ℕ} {ℕ} { ! } {n} {e} [Γ]₁ (maybeEmbᵛ {A = Univ _ _} [Γ]₁ (Uᵛ emb< [Γ]₁))
                                                                (ℕᵗᵛ [Γ]₁) (ℕᵗᵛ [Γ]₁) [ℕ] [ℕ] [n]ₜ [Id]′ [e]ₜ′)
        [id] , [eq] = redSubstTermᵛ {ℕ} {cast ⁰ ℕ ℕ e (suc n)} {suc (cast ⁰ ℕ ℕ e n)} {∞} [Γ]₁
                                    (λ {Δ} {σ} ⊢Δ [σ] → cast-ℕ-S (⊢eΔ {Δ} {σ} ⊢Δ [σ]) (⊢nΔ {Δ} {σ} ⊢Δ [σ]))
                                    [ℕ] [suc-cast]
    in [Γ]₁ , modelsTermEq [ℕ] [id] [suc-cast] [eq]
  fundamentalTermEq {Γ} (cast-Ind-ctr {ind} {j} {e} {args} {Ts} ind∈ eq ⊢e ⊢args) with fundamentalTerm ⊢e
  ... | [Γ] , [Id] , [e]ₜ =
    let [Ind] = Indᵛ {i = (SU.SInd.name ind)} {l = ∞} [Γ]
        [args]ᵥ = fundamentalAllInd {ind = ind} {j = j} {Ts = Ts} {args = args} [Γ] [Ind] eq ⊢args
        [U] = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ emb< [Γ])
        [Indᵗ] = maybeEmbTermᵛ {A = Univ _ _} {t = Ind (SU.SInd.name ind)} [Γ] (Uᵛ emb< [Γ]) (Indᵗᵛ [Γ])
        castArgs = map (λ a → cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e a) args
        [cast-args]ᵥ = mapCastArgs [Γ] [Ind] [U] [Indᵗ] [Id] [e]ₜ [args]ᵥ
        ⊢cast-args = mapCastAll [Γ] ⊢e (all∈ (SU.ctrArgsTypesPositive ind j Ts eq)) ⊢args
        [ctr-cast] = ctrᵛ {ind = ind} {j = j} {args = castArgs} {Ts = Ts} {l = ∞}
                          [Γ] [Ind] ind∈ eq ⊢cast-args [cast-args]ᵥ
        ⊢eΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([Id] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e]ₜ {Δ} {σ} ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ {Ind (SU.SInd.name ind)} {cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e (ctr (SU.SInd.name ind) j args)}
                                    {ctr (SU.SInd.name ind) j castArgs} {∞} [Γ]
                                    (λ {Δ} {σ} ⊢Δ [σ] →
                                       let step = cast-Ind-ctr ind∈ eq (⊢eΔ {Δ} {σ} ⊢Δ [σ])
                                                              (substAll-ctrArgs {σ = σ} [Γ] ⊢Δ [σ] ⊢args)
                                           lhs≡ = PE.cong (cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) (subst σ e))
                                                          (subst-ctr σ (SU.SInd.name ind) j args)
                                           rhs≡ = PE.trans (subst-ctr σ (SU.SInd.name ind) j castArgs)
                                                    (PE.cong (ctr (SU.SInd.name ind) j)
                                                      (PE.trans (map-map (subst σ) (λ a → cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e a) args)
                                                        (PE.sym (map-map (λ a → cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) (subst σ e) a)
                                                                         (subst σ) args))))
                                       in PE.subst₂ (λ t u → Δ ⊢ t ⇒ u ∷ Ind (SU.SInd.name ind) ^ ι ⁰)
                                            (PE.sym lhs≡) (PE.sym rhs≡) step)
                                    [Ind] [ctr-cast]
    in [Γ] , modelsTermEq [Ind] [id] [ctr-cast] [eq]
    where

      emb-stype-pos : ∀ (T : SU.Type) → SU.isPositive (SU.SInd.name ind) T → emb-stype T PE.≡ Ind (SU.SInd.name ind)
      emb-stype-pos (SU.Ind j′) i≡i = PE.cong Ind (PE.sym i≡i)
      emb-stype-pos (SU.Arrow _ _) ()

      mapCastArgs : ∀ {args′} ([Γ]′ : ⊩ᵛ Γ)
                  → ([Ind]′ : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ]′)
                  → ([U]′ : Γ ⊩ᵛ⟨ ∞ ⟩ Univ ! ⁰ ^ [ ! , ι ¹ ] / [Γ]′)
                  → ([Indᵗ]′ : Γ ⊩ᵛ⟨ ∞ ⟩ Ind (SU.SInd.name ind) ∷ Univ ! ⁰ ^ [ ! , ι ¹ ] / [Γ]′ / [U]′)
                  → ([Id]′ : Γ ⊩ᵛ⟨ ∞ ⟩ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ] / [Γ]′)
                  → ([e]ₜ′ : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ] / [Γ]′ / [Id]′)
                  → All (λ a → Γ ⊩ᵛ⟨ ∞ ⟩ a ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ]′ / [Ind]′) args′
                  → All (λ a → Γ ⊩ᵛ⟨ ∞ ⟩ a ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ]′ / [Ind]′)
                        (map (λ a → cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e a) args′)
      mapCastArgs _ _ _ _ _ _ []ₐ = []ₐ
      mapCastArgs {args′ = a List∷ as} [Γ]′ [Ind]′ [U]′ [Indᵗ]′ [Id]′ [e]ₜ′ ([a]ₜ ∷ₐ [as]ₜ) =
        castᵗᵛ {Ind (SU.SInd.name ind)} {Ind (SU.SInd.name ind)} { ! } {a} {e} [Γ]′ [U]′ [Indᵗ]′ [Indᵗ]′ [Ind]′ [Ind]′ [a]ₜ [Id]′ [e]ₜ′
        ∷ₐ mapCastArgs [Γ]′ [Ind]′ [U]′ [Indᵗ]′ [Id]′ [e]ₜ′ [as]ₜ

      mapCastAll : ([Γ]′ : ⊩ᵛ Γ)
                 → Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ]
                 → ∀ {args′} {Ts : List SU.Type}
                 → All (SU.isPositive (SU.SInd.name ind)) Ts
                 → Γ ⊢All args′ ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
                 → Γ ⊢All map (λ a → cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e a) args′ ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
      mapCastAll _ _ []ₐ εⱼ = εⱼ
      mapCastAll [Γ]′ ⊢e′ (pos ∷ₐ poss) (consⱼ ⊢t ⊢ts) =
        let emb≡Ind = emb-stype-pos _ pos
            ⊢tInd = PE.subst (λ A → _ ⊢ _ ∷ A ^ [ ! , ι ⁰ ]) emb≡Ind ⊢t
            ⊢cast = castⱼ (Indⱼ (soundContext [Γ]′)) (Indⱼ (soundContext [Γ]′)) ⊢e′ ⊢tInd
            ⊢cast′ = PE.subst (λ A → _ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e _ ∷ A ^ [ ! , ι ⁰ ])
                              (PE.sym emb≡Ind) ⊢cast
        in  consⱼ ⊢cast′ (mapCastAll [Γ]′ ⊢e′ poss ⊢ts)
  fundamentalTermEq {Γ} (cast-Π {A} {A'} {rA} {B} {B'} {e} {f} ⊢A ⊢B ⊢A' ⊢B' ⊢e ⊢f)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B' | fundamentalTerm ⊢e | fundamentalTerm ⊢f 
  ... | [ΓA] , [UA] , [A]ₜ | [ΓB] ∙ [AB] , [UB] , [B]ₜ | [ΓA'] , [UA'] , [A']ₜ | [ΓB'] ∙ [AB'] , [UB'] , [B']ₜ | [Γ] , [Id] , [e]ₜ | [Γ]₁ , [ΠAB] , [f]ₜ =
    let [UA]′ = maybeEmbᵛ {A = Univ rA _} [Γ]₁ (Uᵛ emb< [Γ]₁) 
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [Γ]₁ [UA] [UA]′ [A]ₜ
        [A']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A'} [ΓA'] [Γ]₁ [UA'] [UA]′ [A']ₜ
        [A] = maybeEmbᵛ {A = A} [Γ]₁ (univᵛ {A = A} [Γ]₁ (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [A'] = maybeEmbᵛ {A = A'} [Γ]₁ (univᵛ {A = A'} [Γ]₁ (≡is≤ PE.refl) [UA]′ [A']ₜ′)
        [ΓB]₁ = [Γ]₁ ∙ [A]
        [UB]′ = S.irrelevance {A = Univ _ _} {Γ = Γ ∙ A ^ _} ([ΓB] ∙ [AB]) [ΓB]₁ (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} ([ΓB] ∙ [AB]) [ΓB]₁ (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [ΓB']₁ = [Γ]₁ ∙ [A']
        [UB']′ = S.irrelevance {A = Univ _ _} {Γ = Γ ∙ A' ^ _} ([ΓB'] ∙ [AB']) [ΓB']₁ (λ {Δ} {σ} → [UB'] {Δ} {σ}) 
        [B']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B'} ([ΓB'] ∙ [AB']) [ΓB']₁ (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ
        [B']  = maybeEmbᵛ {A = B'} [ΓB']₁ (univᵛ {A = B'} [ΓB']₁ (≡is≤ PE.refl) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ′)
        [Id]′  = S.irrelevance {A = Id (Univ _ _) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰  ° ⁰ ^ !)} [Γ] [Γ]₁ [Id]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _)  (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰  ° ⁰ ^ !)} {t = e} [Γ] [Γ]₁ [Id] [Id]′ [e]ₜ
     in [Γ]₁ , cast-Πᵗᵛ {A} {B} {A'} {B'} {rA} {Γ} {e} {f} [Γ]₁ [A] [A'] (λ {Δ} {σ} → [UB]′ {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ})
                      [A]ₜ′ [B]ₜ′ [A']ₜ′ [B']ₜ′ [Id]′ [e]ₜ′ [ΠAB] [f]ₜ

  fundamentalAllInd {Γ} {ind} {j} {Ts} [Γ] [Ind] eq ⊢args =
    go Ts (all∈ (SU.ctrArgsTypesPositive ind j Ts eq)) ⊢args
    where

      emb-stype-pos : ∀ (T : SU.Type) → SU.isPositive (SU.SInd.name ind) T → emb-stype T PE.≡ Ind (SU.SInd.name ind)
      emb-stype-pos (SU.Ind j′) i≡i = PE.cong Ind (PE.sym i≡i)
      emb-stype-pos (SU.Arrow _ _) ()

      go : ∀ {args} (Ts : List SU.Type)
         → All (SU.isPositive (SU.SInd.name ind)) Ts
         → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
         → All (λ a → Γ ⊩ᵛ⟨ ∞ ⟩ a ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] / [Γ] / [Ind]) args
      go [] []ₐ εⱼ = []ₐ
      go (T List∷ Ts) (pos ∷ₐ poss) (consⱼ {t = t} ⊢t ⊢ts)
        with fundamentalTerm ⊢t
      ... | [Γt] , [A] , [t] =
        let emb≡Ind = emb-stype-pos T pos
            [At]′ = PE.subst (λ A′ → ∃ λ ([A]′ : Γ ⊩ᵛ⟨ ∞ ⟩ A′ ^ [ ! , ι ⁰ ] / [Γt])
                                      → Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A′ ^ [ ! , ι ⁰ ] / [Γt] / [A]′)
                             emb≡Ind ([A] , [t])
            [A]′ = proj₁ [At]′
            [t]′ = proj₂ [At]′
            [t]″ = S.irrelevanceTerm {A = Ind (SU.SInd.name ind)} {t = t} [Γt] [Γ] [A]′ [Ind] [t]′
        in  [t]″ ∷ₐ go Ts poss ⊢ts

  fundamentalAllMethods {Γ} {ind} {P} {rG} {lG} {ms} [Γ] ⊢ms =
    go ms (indRectBranchTyList ind P rG lG) ⊢ms
    where
      go : ∀ ms′ As
         → Γ ⊢All ms′ ∷ As ^ [ rG , ι lG ]
         → All₂ (λ m A → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ rG , ι lG ] / [Γ])
                         → Γ ⊩ᵛ⟨ ∞ ⟩ m ∷ A ^ [ rG , ι lG ] / [Γ] / [A])
                ms′ As
      go [] [] εⱼ = []ₐ
      go (m List∷ ms′) (A List∷ As) (consⱼ ⊢m ⊢ms′)
        with fundamentalTerm ⊢m
      ... | [Γm] , [A] , [m] =
        let [A]′ = S.irrelevance {A = A} [Γm] [Γ] [A]
            [m]′ = S.irrelevanceTerm {A = A} {t = m} [Γm] [Γ] [A] [A]′ [m]
        in  ([A]′ , [m]′) ∷ₐ go ms′ As ⊢ms′
{-
  fundamentalTermEq {Γ} (Id-SProp {A} {B} ⊢A ⊢B) with fundamentalTerm ⊢A | fundamentalTerm ⊢B
  ... | [ΓA] , [UA] , [A]ₜ | [ΓB] , [UB] , [B]ₜ =
    let [SProp] = maybeEmbᵛ {A = SProp} [ΓB] (Uᵛ emb< [ΓB])
        [UA]′ =  maybeEmbᵛ {A = Univ _ _} [ΓB] (Uᵛ emb< [ΓB])
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [ΓB] [UA] [UA]′ [A]ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} [ΓB] [ΓB] [UB] [UA]′ [B]ₜ
        ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA]′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([A]ₜ′ ⊢Δ [σ]))
        [A] = maybeEmbᵛ {A = A} [ΓB] (univᵛ {A = A} [ΓB] (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [B] = maybeEmbᵛ {A = B} [ΓB] (univᵛ {A = B} [ΓB] (≡is≤ PE.refl) [UB] [B]ₜ)
        ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B]ₜ ⊢Δ [σ]))
        _▹▹⁰_ = λ A B → A ^ % ° ⁰ ▹▹ B ° ⁰ ° ⁰ ^ %
        Id-SProp-res = λ A B → (A ▹▹⁰ B) ×× (B ▹▹⁰ A)
        [Id-SProp] : Γ ⊩ᵛ Id (SProp) A B ⇒ Id-SProp-res A B ∷ SProp ^ next ⁰ / [ΓB]
        [Id-SProp] = λ {Δ} {σ} ⊢Δ [σ] → PE.subst (λ ret → Δ ⊢ Id (SProp) (subst σ A) (subst σ B) ⇒ ret ∷ SProp ^ next ⁰ )
                                                 (PE.cong₄ (λ a b c d → ∃ (Π a ^ % ° ⁰ ▹ b ° ⁰ ° ⁰ ^ %) ▹ (Π c ^ % ° ⁰ ▹ d ° ⁰ ° ⁰ ^ %))
                                                           PE.refl (PE.sym (Idsym-subst-lemma σ B)) (PE.sym (Idsym-subst-lemma σ B))
                                                           (PE.trans (PE.cong wk1d (PE.sym (Idsym-subst-lemma σ A))) (PE.sym (Idsym-subst-lemma-wk1d σ (wk1 A)))))
                                                 (Id-SProp {A = subst σ A} {B = subst σ B} (⊢AΔ {Δ} {σ} ⊢Δ [σ]) (⊢BΔ {Δ} {σ} ⊢Δ [σ]))       
        [A▹▹B]ₜ = ▹▹irrᵗᵛ {F = A} {G = B} [ΓB] [A] [UA]′ [A]ₜ′ [B]ₜ′
        [A▹▹B] = maybeEmbᵛ {A = A ▹▹⁰ B} [ΓB] (univᵛ {A = A ▹▹⁰ B} [ΓB] (≡is≤ PE.refl) [SProp] [A▹▹B]ₜ)
        [B▹▹A]ₜ = ▹▹irrᵗᵛ {F = B} {G = A} [ΓB] [B] [UA]′ [B]ₜ′ [A]ₜ′
        [Id-SProp-res] : Γ ⊩ᵛ⟨ ∞ ⟩ Id-SProp-res A B ∷ SProp ^ [ ! , next ⁰ ] / [ΓB] / [SProp]
        [Id-SProp-res] = ××ᵗᵛ {F = A ▹▹⁰ B} {G = B ▹▹⁰ A} [ΓB] [A▹▹B] [A▹▹B]ₜ [B▹▹A]ₜ
        [id] , [eq] = redSubstTermᵛ {SProp} {Id (SProp) A B} {Id-SProp-res A B}
                                    [ΓB] (λ {Δ} {σ} ⊢Δ [σ] → [Id-SProp] {Δ} {σ} ⊢Δ [σ]) 
                                    [SProp] [Id-SProp-res] 
    in [ΓB] , modelsTermEq [SProp] [id] [Id-SProp-res] [eq]
  fundamentalTermEq (Id-U-ΠΠ ⊢A ⊢B ⊢A' ⊢B') with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B'
  fundamentalTermEq (Id-U-ΠΠ {A} {A'} {rA} {B} {B'} ⊢A ⊢B ⊢A' ⊢B') | [Γ] , [UA] , [A]ₜ | [Γ]₁ ∙ [A]₁ , [UB] , [B]ₜ | [Γ]' , [UA'] , [A']ₜ | [Γ]₁' ∙ [A']₁ , [UB'] , [B']ₜ =
    let [A]′  = S.irrelevance {A = A} [Γ] [Γ]₁' (maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ))
        [A']′  = S.irrelevance {A = A'} [Γ]' [Γ]₁' (maybeEmbᵛ {A = A'} [Γ]' (univᵛ {A = A'} [Γ]' (≡is≤ PE.refl) [UA'] [A']ₜ))
        [UB]′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [UB']′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ})
        [U] = maybeEmbᵛ {A = Univ rA _} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]₁' [UA] [U] [A]ₜ
        [A']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A'} [Γ]' [Γ]₁' [UA'] [U] [A']ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B}  (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [B']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B'} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ
    in [Γ]₁' , Id-U-ΠΠᵗᵛ [Γ]₁' [A]′ [A']′ (λ {Δ} {σ} → [UB]′ {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [A]ₜ′ [B]ₜ′ [A']ₜ′ [B']ₜ′
-}

-- Fundamental theorem for substitutions.
fundamentalSubst : ∀ {Γ Δ σ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ∷ Γ
      → ∃ λ [Γ] → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
fundamentalSubst ε ⊢Δ [σ] = ε , tt
fundamentalSubst (⊢Γ ∙ ⊢A) ⊢Δ ([tailσ] , [headσ]) =
  let [Γ] , [A] = fundamental ⊢A
      [Δ] , [A]′ , [t] = fundamentalTerm [headσ]
      [Γ]′ , [σ] = fundamentalSubst ⊢Γ ⊢Δ [tailσ]
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [idA]  = proj₁ ([A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ ([A] ⊢Δ [tailσ]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
  in  [Γ] ∙ [A] , ([tailσ]′
  ,   irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _) [idA] [idA]′ [idt])

subTypeEq ⊢Δ [σ] A≡B =
  let [Γ]   = proj₁ (fundamentalEq A≡B)
      [A]   = proj₁ (proj₂ (fundamentalEq A≡B))
      [A≡B] = proj₂ (proj₂ (proj₂ (fundamentalEq A≡B)))
      [Γ]₁  = proj₁ (fundamentalSubst (wfEq A≡B) ⊢Δ [σ])
      [σ]ᵛ  = proj₂ (fundamentalSubst (wfEq A≡B) ⊢Δ [σ])
      [σ]′  = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]ᵛ
      [Aσ]  = proj₁ ([A] ⊢Δ [σ]′)
  in  escape [Aσ] , ≅-eq (escapeEq [Aσ] ([A≡B] ⊢Δ [σ]′))

-- Fundamental theorem for substitution equality.
fundamentalSubstEq : ∀ {Γ Δ σ σ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
      → ∃₂ λ [Γ] [σ]
      → ∃  λ ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
fundamentalSubstEq ε ⊢Δ σ = ε , tt , tt , tt
fundamentalSubstEq (⊢Γ ∙ ⊢A) ⊢Δ (tailσ≡σ′ , headσ≡σ′) =
  let [Γ] , [A] = fundamental ⊢A
      [Γ]′ , [tailσ] , [tailσ′] , [tailσ≡σ′] = fundamentalSubstEq ⊢Γ ⊢Δ tailσ≡σ′
      [Δ] , modelsTermEq [A]′ [t] [t′] [t≡t′] = fundamentalTermEq headσ≡σ′
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ]
      [tailσ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ′]
      [tailσ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ] [tailσ]′ [tailσ≡σ′]
      [idA]  = proj₁ ([A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ ([A] ⊢Δ [tailσ]′)
      [idA]″ = proj₁ ([A] ⊢Δ [tailσ′]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
      [idt′] = proj₁ ([t′] (soundContext [Δ]) (idSubstS [Δ]))
      [idt≡t′]  = [t≡t′] (soundContext [Δ]) (idSubstS [Δ])
  in  [Γ] ∙ [A]
  ,   ([tailσ]′ , irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _) [idA] [idA]′ [idt])
  ,   ([tailσ′]′ , convTerm₁ [idA]′ [idA]″
                             (proj₂ ([A] ⊢Δ [tailσ]′) [tailσ′]′ [tailσ≡σ′]′)
                             (irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _)
                                                [idA] [idA]′ [idt′]))
  ,   ([tailσ≡σ′]′ , irrelevanceEqTerm″ PE.refl PE.refl (subst-id _) (subst-id _) (subst-id _)
                                         [idA] [idA]′ [idt≡t′])

subTerm [Γ] ⊢Δ [σ] ⊢t =
  let [Γ]₁ = proj₁ (fundamentalTerm ⊢t)
      [A]  = proj₁ (proj₂ (fundamentalTerm ⊢t))
      [t]  = proj₂ (proj₂ (fundamentalTerm ⊢t))
      [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
  in  escapeTerm (proj₁ ([A] ⊢Δ [σ]′)) (proj₁ ([t] ⊢Δ [σ]′))

substAll-ctrArgs {Γ} {Δ} {σ} {Ts} {args} [Γ] ⊢Δ [σ] ⊢args =
  PE.subst (λ As → Δ ⊢All map (subst σ) args ∷ As ^ [ ! , ι ⁰ ])
           (map-subst-emb-stype σ Ts)
           (go ⊢args)
  where
    go : ∀ {args′ As} → Γ ⊢All args′ ∷ As ^ [ ! , ι ⁰ ]
       → Δ ⊢All map (subst σ) args′ ∷ map (subst σ) As ^ [ ! , ι ⁰ ]
    go εⱼ = εⱼ
    go (consⱼ ⊢t ⊢ts) = consⱼ (subTerm [Γ] ⊢Δ [σ] ⊢t) (go ⊢ts)

substAll-indRectBranch {Γ} {Δ} {σ} {ind} {P} {rG} {lG} {ms} [Γ] ⊢Δ [σ] ⊢ms =
  PE.subst (λ As → Δ ⊢All map (subst σ) ms ∷ As ^ [ rG , ι lG ])
           (subst-indRectBranchTyList σ ind P rG lG)
           (go ⊢ms)
  where
    go : ∀ {ms′ As} → Γ ⊢All ms′ ∷ As ^ [ rG , ι lG ]
       → Δ ⊢All map (subst σ) ms′ ∷ map (subst σ) As ^ [ rG , ι lG ]
    go εⱼ = εⱼ
    go (consⱼ ⊢m ⊢ms′) = consⱼ (subTerm [Γ] ⊢Δ [σ] ⊢m) (go ⊢ms′)
