import Definition.SUntyped as SI
module Definition.Equiv (senv : SI.SEnv) where
open import Definition.OUntyped senv
open import Definition.OTyped senv
open import Definition.Sort
import Definition.Untyped senv as U
import Tools.PropositionalEquality as PE
open import Tools.List using (List)

-- An equivalence between ℕ and ℕ.
ℕ→ℕ : Term
ℕ→ℕ = Π ℕ ^ ! ° ⁰ ▹ ℕ ° ⁰ ° ⁰ ^ !

retrTy : Term → Term → Term
retrTy fwd bwd =
  Π ℕ ^ ! ° ⁰ ▹ Id ℕ (var 0) (fwd ∘ (bwd ∘ var 0 ^ ⁰) ^ ⁰) ° ⁰ ° ⁰ ^ %

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

    fwd-emb-subst : ∀ σ → U.subst (U.repeat U.liftSubst σ 0) (U.emb_oterm_term fwd) PE.≡ U.emb_oterm_term fwd
    bwd-emb-subst : ∀ σ → U.subst (U.repeat U.liftSubst σ 0) (U.emb_oterm_term bwd) PE.≡ U.emb_oterm_term bwd

    ⊢fwd  : ∀ {Γ} → ⊢ Γ → Γ ⊢ fwd ∷ ℕ→ℕ ^ [ ! , ι ⁰ ]
    ⊢bwd  : ∀ {Γ} → ⊢ Γ → Γ ⊢ bwd ∷ ℕ→ℕ ^ [ ! , ι ⁰ ]
    ⊢retr : ∀ {Γ} → ⊢ Γ → Γ ⊢ retr ∷ retrTy fwd bwd ^ [ ! , ι ⁰ ]
    ⊢sect : ∀ {Γ} → ⊢ Γ → Γ ⊢ sect ∷ sectTy fwd bwd ^ [ ! , ι ⁰ ]

-- A list of equivalences, as in Uniquevalence.uty, where the typing relation
-- is relative to [list (equiv env)]
Equivs : Set
Equivs = List Equiv
