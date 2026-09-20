import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Properties.Successor (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open EqRelSet {{...}}
open import Definition.Untyped senv
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.Irrelevance senv equivs
open import Definition.LogicalRelation.ShapeView senv equivs
open import Tools.Product
-- Helper function for successors for specific reducible derivations.
sucTerm′ : ∀ {l Γ n}
           ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
         → Γ ⊩⟨ l ⟩ n ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
         → Γ ⊩⟨ l ⟩ suc n ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
sucTerm′ (noemb D) (ℕₜ n [[ ⊢t , ⊢u , d ]] n≡n prop) =
  let natN = natural prop
  in  ℕₜ _ [[ sucⱼ ⊢t , sucⱼ ⊢t , id (sucⱼ ⊢t) ]]
         (≅-suc-cong (≅ₜ-red (red D) d d ℕₙ
                             (naturalWhnf natN) (naturalWhnf natN) n≡n))
         (sucᵣ (ℕₜ n [[ ⊢t , ⊢u , d ]] n≡n prop))
sucTerm′ (emb emb< x) [n] = sucTerm′ x [n]
sucTerm′ (emb ∞< x) [n] = sucTerm′ x [n]

-- Reducible natural numbers can be used to construct reducible successors.
sucTerm : ∀ {l Γ n} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ])
        → Γ ⊩⟨ l ⟩ n ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
        → Γ ⊩⟨ l ⟩ suc n ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
sucTerm [ℕ] [n] =
  let [n]′ = irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n]
  in  irrelevanceTerm (ℕ-intr (ℕ-elim [ℕ]))
                      [ℕ]
                      (sucTerm′ (ℕ-elim [ℕ]) [n]′)

-- Helper function for successor equality for specific reducible derivations.
sucEqTerm′ : ∀ {l Γ n n′}
             ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
           → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
sucEqTerm′ (noemb D) (ℕₜ₌ k k′ [[ ⊢t , ⊢u , d ]]
                              [[ ⊢t₁ , ⊢u₁ , d₁ ]] t≡u prop) =
  let natK , natK′ = split prop
  in  ℕₜ₌ _ _ (idRedTerm:*: (sucⱼ ⊢t)) (idRedTerm:*: (sucⱼ ⊢t₁))
        (≅-suc-cong (≅ₜ-red (red D) d d₁ ℕₙ (naturalWhnf natK) (naturalWhnf natK′) t≡u))
        (sucᵣ (ℕₜ₌ k k′ [[ ⊢t , ⊢u , d ]] [[ ⊢t₁ , ⊢u₁ , d₁ ]] t≡u prop))
sucEqTerm′ (emb emb< x) [n≡n′] = sucEqTerm′ x [n≡n′]
sucEqTerm′ (emb ∞< x) [n≡n′] = sucEqTerm′ x [n≡n′]

-- Reducible natural number equality can be used to construct reducible equality
-- of the successors of the numbers.
sucEqTerm : ∀ {l Γ n n′} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ] )
          → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
          → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
sucEqTerm [ℕ] [n≡n′] =
  let [n≡n′]′ = irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n≡n′]
  in  irrelevanceEqTerm (ℕ-intr (ℕ-elim [ℕ])) [ℕ]
                        (sucEqTerm′ (ℕ-elim [ℕ]) [n≡n′]′)
