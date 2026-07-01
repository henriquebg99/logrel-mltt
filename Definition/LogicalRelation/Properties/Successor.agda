{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Properties.Successor (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.Irrelevance equiv
open import Definition.LogicalRelation.ShapeView equiv

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

-- Helper function for successors for specific reducible derivations.
suc2Term′ : ∀ {l Γ n}
           ([ℕ2] : Γ ⊩⟨ l ⟩ℕ2 ℕ2)
         → Γ ⊩⟨ l ⟩ n ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2-intr [ℕ2]
         → Γ ⊩⟨ l ⟩ suc2 n ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2-intr [ℕ2]
suc2Term′ (noemb D) (ℕ2ₜ n [[ ⊢t , ⊢u , d ]] n≡n prop) =
  let natN = natural2 prop
  in  ℕ2ₜ _ [[ suc2ⱼ ⊢t , suc2ⱼ ⊢t , id (suc2ⱼ ⊢t) ]]
         (≅-suc2-cong (≅ₜ-red (red D) d d ℕ2ₙ
                             (natural2Whnf natN) (natural2Whnf natN) n≡n))
         (suc2ᵣ (ℕ2ₜ n [[ ⊢t , ⊢u , d ]] n≡n prop))
suc2Term′ (emb emb< x) [n] = suc2Term′ x [n]
suc2Term′ (emb ∞< x) [n] = suc2Term′ x [n]

-- Reducible second natural numbers can be used to construct reducible successors.
suc2Term : ∀ {l Γ n} ([ℕ2] : Γ ⊩⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ])
        → Γ ⊩⟨ l ⟩ n ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
        → Γ ⊩⟨ l ⟩ suc2 n ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
suc2Term [ℕ2] [n] =
  let [n]′ = irrelevanceTerm [ℕ2] (ℕ2-intr (ℕ2-elim [ℕ2])) [n]
  in  irrelevanceTerm (ℕ2-intr (ℕ2-elim [ℕ2]))
                      [ℕ2]
                      (suc2Term′ (ℕ2-elim [ℕ2]) [n]′)

-- Helper function for successor equality for specific reducible derivations.
suc2EqTerm′ : ∀ {l Γ n n′}
             ([ℕ2] : Γ ⊩⟨ l ⟩ℕ2 ℕ2)
           → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2-intr [ℕ2]
           → Γ ⊩⟨ l ⟩ suc2 n ≡ suc2 n′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2-intr [ℕ2]
suc2EqTerm′ (noemb D) (ℕ2ₜ₌ k k′ [[ ⊢t , ⊢u , d ]]
                              [[ ⊢t₁ , ⊢u₁ , d₁ ]] t≡u prop) =
  let natK , natK′ = split2 prop
  in  ℕ2ₜ₌ _ _ (idRedTerm:*: (suc2ⱼ ⊢t)) (idRedTerm:*: (suc2ⱼ ⊢t₁))
        (≅-suc2-cong (≅ₜ-red (red D) d d₁ ℕ2ₙ (natural2Whnf natK) (natural2Whnf natK′) t≡u))
        (suc2ᵣ (ℕ2ₜ₌ k k′ [[ ⊢t , ⊢u , d ]] [[ ⊢t₁ , ⊢u₁ , d₁ ]] t≡u prop))
suc2EqTerm′ (emb emb< x) [n≡n′] = suc2EqTerm′ x [n≡n′]
suc2EqTerm′ (emb ∞< x) [n≡n′] = suc2EqTerm′ x [n≡n′]

-- Reducible second natural number equality can be used to construct reducible equality
-- of the successors of the numbers.
suc2EqTerm : ∀ {l Γ n n′} ([ℕ2] : Γ ⊩⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] )
          → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
          → Γ ⊩⟨ l ⟩ suc2 n ≡ suc2 n′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
suc2EqTerm [ℕ2] [n≡n′] =
  let [n≡n′]′ = irrelevanceEqTerm [ℕ2] (ℕ2-intr (ℕ2-elim [ℕ2])) [n≡n′]
  in  irrelevanceEqTerm (ℕ2-intr (ℕ2-elim [ℕ2])) [ℕ2]
                        (suc2EqTerm′ (ℕ2-elim [ℕ2]) [n≡n′]′)
