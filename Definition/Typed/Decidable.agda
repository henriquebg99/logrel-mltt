import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Decidable (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Decidable senv swf equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.Consequences.Completeness senv swf equivs
open import Tools.Nullary
open import Tools.Product
open import Tools.Nat
-- Decidability of conversion of well-formed types
dec : ∀ {A B r Γ} → Γ ⊢ A ^ r → Γ ⊢ B ^ r → Dec (Γ ⊢ A ≡ B ^ r)
dec ⊢A ⊢B =
  let ⊢Γ≡Γ = reflConEq (wf ⊢A)
  in  map soundnessConv↑ completeEq
          (decConv↑ ⊢Γ≡Γ (completeEq (refl ⊢A)) (completeEq (refl ⊢B)) (le-suc (le-refl _) ))

-- Decidability of conversion of well-formed terms
decTerm : ∀ {t u A r Γ} → Γ ⊢ t ∷ A ^ r → Γ ⊢ u ∷ A ^ r → Dec (Γ ⊢ t ≡ u ∷ A ^ r)
decTerm {r = [ ! , l ]} ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map soundnessConv↑Term completeEqTerm
          (decConv↑TermConv ⊢Γ≡Γ (refl (syntacticTerm ⊢t)) (completeEqTerm (genRefl ⊢t)) (completeEqTerm (genRefl ⊢u)) (le-suc (le-refl _) ))
decTerm {r = [ % , l ]} ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map (λ x → proj₂ (proj₂ (soundness~↑% x))) completeEqTerm
          (decConv↑TermConv ⊢Γ≡Γ (refl (syntacticTerm ⊢t)) (completeEqTerm (genRefl ⊢t)) (completeEqTerm (genRefl ⊢u)) (le-suc (le-refl _) ))
