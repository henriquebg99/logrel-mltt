{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Substitution.Reducibility (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed equiv
open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.Irrelevance equiv
open import Definition.LogicalRelation.Substitution equiv
open import Definition.LogicalRelation.Substitution.Properties equiv

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Valid types are reducible.
reducibleᵛ : ∀ {A rA Γ l}
             ([Γ] : ⊩ᵛ Γ)
           → Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]
           → Γ ⊩⟨ l ⟩ A ^ rA
reducibleᵛ [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ [id]))

-- Valid type equality is reducible.
reducibleEqᵛ : ∀ {A B rA Γ l}
               ([Γ] : ⊩ᵛ Γ)
               ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
             → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ rA / [Γ] / [A]
             → Γ ⊩⟨ l ⟩ A ≡ B ^ rA / reducibleᵛ [Γ] [A]
reducibleEqᵛ {A = A} [Γ] [A] [A≡B] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEq″ (subst-id _) (subst-id _) PE.refl PE.refl
                     (proj₁ ([A] ⊢Γ [id])) [σA] ([A≡B] ⊢Γ [id])

-- Valid terms are reducible.
reducibleTermᵛ : ∀ {t A rA Γ l}
                 ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ rA / [Γ] / [A]
               → Γ ⊩⟨ l ⟩ t ∷ A ^ rA / reducibleᵛ [Γ] [A]
reducibleTermᵛ {A = A} [Γ] [A] [t] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _)
                        (proj₁ ([A] ⊢Γ [id])) [σA] (proj₁ ([t] ⊢Γ [id]))

-- Valid term equality is reducible.
reducibleEqTermᵛ : ∀ {t u A rA Γ l}
                   ([Γ] : ⊩ᵛ Γ)
                   ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
                 → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ rA / [Γ] / [A]
                 → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ rA / reducibleᵛ [Γ] [A]
reducibleEqTermᵛ {A = A} [Γ] [A] [t≡u] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEqTerm″ PE.refl PE.refl (subst-id _) (subst-id _) (subst-id _)
                          (proj₁ ([A] ⊢Γ [id])) [σA] ([t≡u] ⊢Γ [id])
