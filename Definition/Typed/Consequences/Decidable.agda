import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.Decidable (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.EqRelInstance senv equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Decidable senv swf equivs
open import Definition.Conversion.Consequences.Completeness senv swf equivs
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE
-- Decidability of algorithmic equality of neutrals.
dec-aux : ∀ {Γ t u T l}
        → Dec (Γ ⊢ t [conv↑] u ∷ T ^ l)
        → Dec (Γ ⊢ t ≡ u ∷ T ^ [ ! , l ])
dec-aux (yes p) = yes (soundnessConv↑Term p)
dec-aux (no ¬p) = no λ x → ¬p (completeEqTerm x)


dec : ∀ {Γ t u T l}
        → (⊢t : Γ ⊢ t ∷ T ^ [ ! , l ])
        → (⊢u : Γ ⊢ u ∷ T ^ [ ! , l ])
        → Dec (Γ ⊢ t ≡ u ∷ T ^ [ ! , l ])
dec ⊢t ⊢u = dec-aux (decConv↑Term (reflConEq (wfTerm ⊢t)) (completeEqTerm (refl ⊢t)) (completeEqTerm (refl ⊢u)) (le-refl _))
