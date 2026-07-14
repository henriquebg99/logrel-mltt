module Definition.STyped where

open import Definition.SUntyped
open import Tools.Nat using (Nat)
open import Tools.List

infixr 30 _∙_
infix  30 _∷_∈_

SCon : Set
SCon = List SType

_∙_ : SType → SCon → SCon
A ∙ Γ = A ∷ Γ

-- Well-typed variables
data _∷_∈_ : Nat → SType → SCon → Set where
  here  : ∀ {Γ A}                     →         0 ∷ A ∈ (A ∙ Γ)
  there : ∀ {Γ A B x} (h : x ∷ A ∈ Γ) → Nat.suc x ∷ A ∈ (B ∙ Γ)

mutual
  -- Well-typed lists of terms
  data _⊢All_∷_ (Γ : SCon) : List STerm → List SType → Set where
    εⱼ   : Γ ⊢All [] ∷ []
    _,ⱼ  : ∀ {t ts A As}
         → Γ ⊢ t ∷ A
         → Γ ⊢All ts ∷ As
         → Γ ⊢All (t ∷ ts) ∷ (A ∷ As)

  -- Well-formed term of a type
  data _⊢_∷_ (Γ : SCon) : STerm → SType → Set where
    varⱼ  : ∀ {x A}
          → x ∷ A ∈ Γ
          → Γ ⊢ sVar x ∷ A
    appⱼ  : ∀ {f a A B}
          → Γ ⊢ f ∷ sArrow A B
          → Γ ⊢ a ∷ A
          → Γ ⊢ sApp f a ∷ B
    lamⱼ  : ∀ {A B t}
          → (A ∙ Γ) ⊢ t ∷ B
          → Γ ⊢ sLam A t ∷ sArrow A B
    ctrⱼ  : ∀ {i j args}
          → Γ ⊢All args ∷ sCtr_args_type_list i j
          → Γ ⊢ sCtr i j args ∷ sInd i
