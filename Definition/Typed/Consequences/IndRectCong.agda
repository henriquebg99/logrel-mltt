import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.IndRectCong (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Typed.EqRelInstance senv equivs
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Substitution senv swf equivs
import Definition.Typed.IndRectCong senv swf equivs as I
open import Tools.Product
open import Tools.List using (_∈ₗ_)
import Definition.SUntyped as SU

-- Congruence of the type of the methods in IndRect.  The induction over the
-- branch types lives in Definition.Typed.IndRectCong (Fundamental needs it
-- too); here we only feed it the congruence of the motive under a
-- substitution.
indRectBranchTyListCong : ∀ {Γ ind P P′ lG ms ms′}
  → ind ∈ₗ senv
  → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ≡ P′ ^ [ ! , ι lG ]
  → Γ ⊢All ms ≡ ms′ ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
  → Γ ⊢All ms ≡ ms′ ∷ indRectBranchTyList ind P′ ! lG ^ [ ! , ι lG ]
indRectBranchTyListCong ind∈ P≡P′ ⊢ms≡ =
  I.indRectBranchTyListCong ind∈ P≡P′
    (λ d ⊢Δ [σ] ⊢u → let Pu≡P′u = substitutionEq P≡P′ (substRefl ([σ] , ⊢u)) ⊢Δ
                     in  proj₁ (syntacticEq Pu≡P′u) , Pu≡P′u)
    ⊢ms≡
