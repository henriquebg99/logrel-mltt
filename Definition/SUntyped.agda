module Definition.SUntyped where

open import Tools.Nat
open import Tools.List
open import Tools.Maybe
open import Tools.Inequality using (Bool; true; false; eqb; if_then_else_)
open import Tools.Product
open import Tools.Empty
open import Tools.Unit
open import Tools.PropositionalEquality

-- Simple types
data Type : Set where
  Ind : Nat → Type  -- index for the inductive type
  Arrow : Type → Type → Type

-- A property for types that do not contain [Ind i]
indNotInType : Nat → Type → Set
indNotInType i (Ind j)     = i ≢ j
indNotInType i (Arrow A B) = indNotInType i A × indNotInType i B

-- TODO explain why we rule out arrows
isPositive : Nat → Type → Set
isPositive ind (Ind _)  = ⊤
isPositive ind (Arrow _ _) = ⊥

-- The description of an inductive type.  The levels of inductive types are
-- always zero, so they are not recorded.
record SInd : Set where
  field
    -- the nat that represents the inductive type
    name : Nat

    -- each list represents the types of arguments for a constructor
    ctrArgsTypes : List (List Type)

    -- a proof that each argument type is positive
    ctrArgsPositive : ∀ Ts → Ts ∈ₗ ctrArgsTypes
                    → ∀ T → T ∈ₗ Ts → isPositive name T

-- An environment of inductive types
SEnv : Set
SEnv = List SInd

-- The names of the inductive types declared in an environment
indNames : SEnv → List Nat
indNames senv = map SInd.name senv

-- Every inductive type occurring in a type is declared in the environment
indsInSEnv : SEnv → Type → Set
indsInSEnv senv (Ind i)     = i ∈ₗ indNames senv
indsInSEnv senv (Arrow A B) = indsInSEnv senv A × indsInSEnv senv B

-- A well-formed environment: no two inductive types share a name, and every
-- inductive type occurring in a constructor argument is declared
swfenv : SEnv → Set
swfenv senv =
  NoDup (indNames senv)
  × All (λ ind → All (λ Ts → All (indsInSEnv senv) Ts) (SInd.ctrArgsTypes ind)) senv

-- In a well-formed environment the name determines the inductive type
name-inj : ∀ senv {ind ind′} → NoDup (indNames senv)
         → ind ∈ₗ senv → ind′ ∈ₗ senv → SInd.name ind ≡ SInd.name ind′ → ind ≡ ind′
name-inj [] _ () _ _
name-inj (x ∷ xs) (nd ∷ₙ _)   hereₗ      hereₗ       eq = refl
name-inj (x ∷ xs) (nd ∷ₙ _)   hereₗ      (thereₗ h′) eq =
  ⊥-elim (nd (subst (λ n → n ∈ₗ indNames xs) (sym eq) (∈ₗ-map SInd.name h′)))
name-inj (x ∷ xs) (nd ∷ₙ _)   (thereₗ h) hereₗ       eq =
  ⊥-elim (nd (subst (λ n → n ∈ₗ indNames xs) eq (∈ₗ-map SInd.name h)))
name-inj (x ∷ xs) (_  ∷ₙ nds) (thereₗ h) (thereₗ h′) eq = name-inj xs nds h h′ eq

-- Syntax of simple terms
data Term : Set where
  var : Nat → Term
  app : Term → Term → Term
  lam : Type → Term → Term
  ctr : Nat → Nat → List Term → Term
  IndRect : Nat → Type → Term → List Term → Term
  -- IndRect i P t ms  — non-dependent elimination of t : Ind i into P

-- The number of constructors of the inductive type
indCtrCount : SInd → Nat
indCtrCount sind = length (SInd.ctrArgsTypes sind)

-- The types of the arguments of constructor [n], [nothing] if there is no
-- such constructor
ctrArgsTypeList : SInd → Nat → Maybe (List Type)
ctrArgsTypeList sind n = nth (SInd.ctrArgsTypes sind) n

ctrArgsTypesPositive : ∀ sind n Ts → ctrArgsTypeList sind n ≡ just Ts
                     → ∀ T → T ∈ₗ Ts → isPositive (SInd.name sind) T
ctrArgsTypesPositive sind n Ts eq =
  SInd.ctrArgsPositive sind Ts (nth-∈ₗ (SInd.ctrArgsTypes sind) n eq)

-- [n] non-dependent [Arrow A] around [B]
arrowRepeat : Nat → Type → Type → Type
arrowRepeat 0       A B = B
arrowRepeat (1+ n) A B = Arrow A (arrowRepeat n A B)

ctrArgIsRecursive : Nat → Type → Bool
ctrArgIsRecursive ind (Ind j)     = eqb j ind
ctrArgIsRecursive _   (Arrow _ _) = false

arrows : List Type → Type → Type
arrows []       B = B
arrows (A ∷ As) B = Arrow A (arrows As B)

recCountList : Nat → List Type → Nat
recCountList i [] = 0
recCountList i (T ∷ Ts) = if ctrArgIsRecursive i T then 1+ (recCountList i Ts) else recCountList i Ts

-- Simply-typed method type for a constructor of [ind] with argument types
-- [Ts] at motive [T]: [A0 → … → A_{n-1} → T → … → T → T] with one [T] per
-- recursive argument
indRectBranchTy : Nat → List Type → Type → Type
indRectBranchTy ind Ts T = arrows Ts (arrowRepeat (recCountList ind Ts) T T)

-- One method type per constructor of the inductive type
indRectBranchTypeList : SInd → Type → List Type
indRectBranchTypeList sind T =
  map (λ Ts → indRectBranchTy (SInd.name sind) Ts T) (SInd.ctrArgsTypes sind)
