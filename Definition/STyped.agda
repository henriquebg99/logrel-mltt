import Definition.SUntyped as SI
module Definition.STyped (senv : SI.SEnv) where

open import Definition.SUntyped
open import Tools.Nat using (Nat; _<<_)
open import Tools.List
open import Tools.Maybe using (just)
open import Tools.PropositionalEquality using (_≡_)

infixr 30 _∙_
infix  30 _∷_∈_

Con : Set
Con = List Type

_∙_ : Type → Con → Con
A ∙ Γ = A ∷ Γ

-- Well-typed variables
data _∷_∈_ : Nat → Type → Con → Set where
  here  : ∀ {Γ A}                     →         0 ∷ A ∈ (A ∙ Γ)
  there : ∀ {Γ A B x} (h : x ∷ A ∈ Γ) → Nat.suc x ∷ A ∈ (B ∙ Γ)

mutual
  -- Well-typed lists of terms
  data _⊢All_∷_ (Γ : Con) : List Term → List Type → Set where
    εⱼ   : Γ ⊢All [] ∷ []
    consⱼ  : ∀ {t ts A As}
         → Γ ⊢ t ∷ A
         → Γ ⊢All ts ∷ As
         → Γ ⊢All (t ∷ ts) ∷ (A ∷ As)

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : Con) : Term → Type → Set where
    varⱼ  : ∀ {x A}
          → x ∷ A ∈ Γ
          → Γ ⊢ var x ∷ A
    appⱼ  : ∀ {f a A B}
          → Γ ⊢ f ∷ Arrow A B
          → Γ ⊢ a ∷ A
          → Γ ⊢ app f a ∷ B
    lamⱼ  : ∀ {A B t}
          → (A ∙ Γ) ⊢ t ∷ B
          → Γ ⊢ lam A t ∷ Arrow A B
    ctrⱼ  : ∀ {ind j args Ts}
          → ind ∈ₗ senv
          → ctrArgsTypeList ind j ≡ just Ts
          → length args ≡ length Ts
          → Γ ⊢All args ∷ Ts
          → Γ ⊢ ctr (SInd.name ind) j args ∷ Ind (SInd.name ind)
    indRectⱼ : ∀ {ind P t ms}
          → ind ∈ₗ senv
          → indsInSEnv senv P
          → Γ ⊢ t ∷ Ind (SInd.name ind)
          → Γ ⊢All ms ∷ indRectBranchTypeList ind P
          → Γ ⊢ IndRect (SInd.name ind) P t ms ∷ P
