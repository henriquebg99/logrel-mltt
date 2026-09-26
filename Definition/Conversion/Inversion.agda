import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.Inversion (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.RedSteps senv equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.Conversion senv swf equivs
open import Definition.Conversion.Whnf senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Reduction senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
import Definition.Typed.Consequences.Inequality senv swf equivs as WF
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.SucCong senv swf equivs
open import Definition.Typed.Consequences.RelevanceUnicity senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Tools.Empty
import Tools.PropositionalEquality as PE
abstract
  [conv↓]ne : ∀ {Γ t u A l} → Neutral A → Γ ⊢ t [conv↓] u ∷ A ^ l → ∃ λ B → Γ ⊢ t ~ u ↓! B ^ l × Γ ⊢ A ≡ B ^ [ ! , l ]
  [conv↓]ne neA (ne-ins x x₁ x₂ x₃) =
    let t~u = (ne-ins x x₁ x₂ x₃)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t~u)
        _ , nft , _ = whnfConv↓Term t~u
        net = inversion-ne neA nft ⊢t
        _ , ⊢t' , _ = syntacticEqTerm (soundness~↓! x₃)
        _ , eq = neTypeEq net ⊢t ⊢t'
    in _ , x₃ , eq

whnfconv↑conv↓ : ∀ {t u A l Γ} → Whnf A → Whnf t → Whnf u → Γ ⊢ t [genconv↑] u ∷ A ^ [ ! , l ] → Γ ⊢ t [conv↓] u ∷ A ^ l
whnfconv↑conv↓ whnfA whnft whnfu ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                rewrite whnfRed*Term d whnft | whnfRed*Term d′ whnfu | whnfRed* D whnfA = t<>u

neutralconv↓ : ∀ {t u l' l Γ} → Neutral t → Neutral u → Γ ⊢ t [conv↓] u ∷ U l' ^  l → Γ ⊢ t ~ u ↓! U l' ^ l
neutralconv↓ net neu (ne x) = x

neutralℕconv↓ : ∀ {t u l Γ} → Neutral t → Neutral u → Γ ⊢ t [conv↓] u ∷ ℕ ^  l → Γ ⊢ t ~ u ↓! ℕ ^ l
neutralℕconv↓ net neu (ℕ-ins x) = x

neutral↓↑ : ∀ {Γ t u A l} → Γ ⊢ t ~ u ↓! A ^ l → ∃ λ B → Γ ⊢ t ~ u ↑! B ^ l
neutral↓↑ ([~] A D whnfB k~l) = _ , k~l
