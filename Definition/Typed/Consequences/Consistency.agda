import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.Consistency (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.EqRelInstance senv equivs
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.Irrelevance senv equivs
open import Definition.LogicalRelation.ShapeView senv equivs
open import Definition.LogicalRelation.Fundamental.Reducibility senv swf equivs
open import Tools.Empty
open import Tools.Product
import Tools.PropositionalEquality as PE
zero≢one′ : ∀ {Γ l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ zero ≡ suc zero ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ] → ⊥
zero≢one′ (noemb x) (ℕₜ₌ .(suc _) .(suc _) d d′ k≡k′ (sucᵣ x₁)) =
  zero≢suc (whnfRed*Term (redₜ d) zeroₙ)
zero≢one′ (noemb x) (ℕₜ₌ .zero .zero d d′ k≡k′ zeroᵣ) =
  zero≢suc (PE.sym (whnfRed*Term (redₜ d′) sucₙ))
zero≢one′ (noemb x) (ℕₜ₌ k k′ d d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) =
  zero≢ne neK (whnfRed*Term (redₜ d) zeroₙ)
zero≢one′ (emb emb< [ℕ]) n = zero≢one′ [ℕ] n
zero≢one′ (emb ∞< [ℕ]) n = zero≢one′ [ℕ] n

-- Zero cannot be judgmentally equal to one.
zero≢one : ∀ {Γ} → Γ ⊢ zero ≡ suc zero ∷ ℕ ^ [ ! , ι ⁰ ] → ⊥
zero≢one 0≡1 =
  let [ℕ] , [0≡1] = reducibleEqTerm 0≡1
  in  zero≢one′ (ℕ-elim [ℕ]) (irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [0≡1])
