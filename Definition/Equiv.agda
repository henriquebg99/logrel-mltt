{-# OPTIONS --safe #-}

module Definition.Equiv where

open import Definition.OUntyped
open import Definition.OTyped
open import Definition.Sort
import Tools.PropositionalEquality as PE

-- An equivalence between ℕ and ℕ2.

ℕ→ℕ2 : Term
ℕ→ℕ2 = Π ℕ ^ ! ° ⁰ ▹ ℕ2 ° ⁰ ° ⁰ ^ !

ℕ2→ℕ : Term
ℕ2→ℕ = Π ℕ2 ^ ! ° ⁰ ▹ ℕ ° ⁰ ° ⁰ ^ !

retrTy : Term → Term → Term
retrTy fwd bwd =
  Π ℕ2 ^ ! ° ⁰ ▹ Id ℕ2 (var 0) (fwd ∘ (bwd ∘ var 0 ^ ⁰) ^ ⁰) ° ⁰ ° ⁰ ^ %

sectTy : Term → Term → Term
sectTy fwd bwd =
  Π ℕ ^ ! ° ⁰ ▹ Id ℕ (var 0) (bwd ∘ (fwd ∘ var 0 ^ ⁰) ^ ⁰) ° ⁰ ° ⁰ ^ %

record Equiv : Set where
  field
    fwd  : Term
    bwd  : Term
    retr : Term
    sect : Term

    fwd-wk : ∀ ρ → wk ρ fwd PE.≡ fwd
    bwd-wk : ∀ ρ → wk ρ bwd PE.≡ bwd

    ⊢fwd  : ∀ {Γ} → ⊢ Γ → Γ ⊢ fwd ∷ ℕ→ℕ2 ^ [ ! , ι ⁰ ]
    ⊢bwd  : ∀ {Γ} → ⊢ Γ → Γ ⊢ bwd ∷ ℕ2→ℕ ^ [ ! , ι ⁰ ]
    ⊢retr : ∀ {Γ} → ⊢ Γ → Γ ⊢ retr ∷ retrTy fwd bwd ^ [ ! , ι ⁰ ]
    ⊢sect : ∀ {Γ} → ⊢ Γ → Γ ⊢ sect ∷ sectTy fwd bwd ^ [ ! , ι ⁰ ]

