module Definition.STyped where

open import Definition.SUntyped
open import Tools.Nat using (Nat)
open import Tools.List

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
    ctrⱼ  : ∀ {i j args}
          → Γ ⊢All args ∷ map Ind (ctrArgsTypeList i j)
          → Γ ⊢ ctr i j args ∷ Ind i
    indRectⱼ : ∀ {i P t ms}
          → Γ ⊢ t ∷ Ind i
          → Γ ⊢All ms ∷ indRectMethodTypeList i P
          → Γ ⊢ IndRect i P t ms ∷ P
