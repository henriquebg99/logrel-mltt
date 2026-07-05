{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
import Definition.LogicalRelation.EquivRed as ERd
module Definition.LogicalRelation.Fundamental.Reducibility (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} {{equivRed : ERd.EquivRed equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.Substitution equiv
open import Definition.LogicalRelation.Substitution.Reducibility equiv
open import Definition.LogicalRelation.Fundamental equiv

open import Tools.Product


-- Well-formed types are reducible.
reducible : ∀ {A rA Γ} → Γ ⊢ A ^ rA → Γ ⊩⟨ ∞ ⟩ A ^ rA
reducible A = let [Γ] , [A] = fundamental A
              in  reducibleᵛ [Γ] [A]

-- Well-formed equality is reducible.
reducibleEq : ∀ {A B rA Γ} → Γ ⊢ A ≡ B ^ rA
            → ∃₂ λ [A] ([B] : Γ ⊩⟨ ∞ ⟩ B ^ rA) → Γ ⊩⟨ ∞ ⟩ A ≡ B ^ rA / [A]
reducibleEq {A} {B} A≡B =
  let [Γ] , [A] , [B] , [A≡B] = fundamentalEq A≡B
  in  reducibleᵛ [Γ] [A]
  ,   reducibleᵛ [Γ] [B]
  ,   reducibleEqᵛ {A} {B} [Γ] [A] [A≡B]

-- Well-formed terms are reducible.
reducibleTerm : ∀ {t A rA Γ} → Γ ⊢ t ∷ A ^ rA → ∃ λ [A] → Γ ⊩⟨ ∞ ⟩ t ∷ A ^ rA / [A]
reducibleTerm {t} {A} ⊢t =
  let [Γ] , [A] , [t] = fundamentalTerm ⊢t
  in  reducibleᵛ [Γ] [A] , reducibleTermᵛ {t} {A} [Γ] [A] [t]

-- Well-formed term equality is reducible.
reducibleEqTerm : ∀ {t u A rA Γ} → Γ ⊢ t ≡ u ∷ A ^ rA → ∃ λ [A] → Γ ⊩⟨ ∞ ⟩ t ≡ u ∷ A ^ rA / [A]
reducibleEqTerm {t} {u} {A} t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  reducibleᵛ [Γ] [A] , reducibleEqTermᵛ {t} {u} {A} [Γ] [A] [t≡u]
