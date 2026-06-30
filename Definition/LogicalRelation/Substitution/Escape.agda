{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Substitution.Escape (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties

open import Definition.Typed equiv

open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.Irrelevance equiv
open import Definition.LogicalRelation.Properties equiv
open import Definition.LogicalRelation.Substitution equiv
open import Definition.LogicalRelation.Substitution.Properties equiv
import Tools.PropositionalEquality as PE

open import Tools.Product


-- Valid types are well-formed.
escapeᵛ : ∀ {A rA l Γ} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ] → Γ ⊢ A ^ rA
escapeᵛ [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
  in  escape (irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ idSubst)))

-- Valid type equality respects the equality relation.
escapeEqᵛ : ∀ {A B rA l Γ} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ rA / [Γ] / [A] → Γ ⊢ A ≅ B ^ rA
escapeEqᵛ [Γ] [A] [A≡B] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) [idA]
  in  escapeEq [idA]′ (irrelevanceEq″ (subst-id _) (subst-id _) PE.refl PE.refl
                                           [idA] [idA]′ ([A≡B] ⊢Γ idSubst))

-- Valid terms are well-formed.
escapeTermᵛ : ∀ {t A rA l Γ} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ rA / [Γ] / [A] → Γ ⊢ t ∷ A ^ rA
escapeTermᵛ [Γ] [A] [t] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ idSubst))
  in  escapeTerm [idA]′
                    (irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _)
                                       [idA] [idA]′ (proj₁ ([t] ⊢Γ idSubst)))

-- Valid term equality respects the equality relation.
escapeEqTermᵛ : ∀ {t u A rA l Γ} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ rA / [Γ] / [A] → Γ ⊢ t ≅ u ∷ A ^ rA
escapeEqTermᵛ [Γ] [A] [t≡u] =
  let ⊢Γ = soundContext [Γ]
      idSubst = idSubstS [Γ]
      [idA]  = proj₁ ([A] ⊢Γ idSubst)
      [idA]′ = irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ idSubst))
  in  escapeTermEq [idA]′
                       (irrelevanceEqTerm″ PE.refl PE.refl (subst-id _) (subst-id _)
                                            (subst-id _)
                                            [idA] [idA]′ ([t≡u] ⊢Γ idSubst))
