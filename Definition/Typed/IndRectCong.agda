import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.IndRectCong (senv : SI.SEnv) (equivs : E.Equivs senv) where

open import Definition.Untyped senv
open import Definition.Typed senv equivs

-- Congruence of the branch-type list under equality of the motive P.
-- The branch types only use P through applications wk1^ n P ∘ <neutral> ^ ¹
-- buried in a nested Π-chain, so transporting indRectBranchTy i j P to a
-- convertible P' needs a genuine (large) induction.  We keep it as a
-- postulate here, with ms/ms' in the same orientation (callers apply symAll
-- to flip them).  It lives in this small module because both
-- Definition.Conversion.Symmetry and Definition.LogicalRelation.Fundamental
-- need it, and those two cannot import each other.
postulate
  indRectBranchTyListCong : ∀ {Γ ind P P' lG ms ms'}
    → Γ ⊢ P ≡ P' ∷ Π Ind (SI.SInd.name ind) ^ ! ° ⁰ ▹ Univ ! lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ]
    → Γ ⊢All ms ≡ ms' ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
    → Γ ⊢All ms ≡ ms' ∷ indRectBranchTyList ind P' ! lG ^ [ ! , ι lG ]
