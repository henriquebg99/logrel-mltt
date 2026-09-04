module Definition.SUntyped where

open import Tools.Nat
open import Tools.List
open import Tools.Inequality using (Bool; true; false; eqb; if_then_else_)
open import Tools.Product
open import Tools.Empty
open import Tools.PropositionalEquality

data Type : Set where
  Ind : Nat → Type  -- index for the inductive type
  Arrow : Type → Type → Type

-- Syntax of simple terms
data Term : Set where
  var : Nat → Term
  app : Term → Term → Term
  lam : Type → Term → Term
  ctr : Nat → Nat → List Term → Term
  IndRect : Nat → Type → Term → List Term → Term
  -- IndRect i P t ms  — non-dependent elimination of t : Ind i into P

-- The definition of the inductive types is parametrized
postulate indCtrCount : Nat → Nat
postulate indLevel : Nat → Nat
postulate ctrArgsTypeList : Nat → Nat → List Type

-- A property for types that do not contain [Ind i]
indNotInType : Nat → Type → Set
indNotInType i (Ind j)     = i ≢ j
indNotInType i (Arrow A B) = indNotInType i A × indNotInType i B

isPositive : Nat → Type → Set
isPositive ind (Ind ind′)  = ind ≡ ind′
isPositive ind (Arrow _ _) = ⊥

postulate
  ctrArgsTypesPositive : ∀ ind n T → T ∈ₗ ctrArgsTypeList ind n → isPositive ind T

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

-- number of recursive arguments in a specific constructor
ctrRecCount : Nat → Nat → Nat
ctrRecCount ind index = recCountList ind (ctrArgsTypeList ind index)

-- Simply-typed method type for constructor [index] of [ind] at motive [T]:
-- [A0 → … → A_{n-1} → T → … → T → T] with one [T] per recursive argument
indRectBranchTy : Nat → Nat → Type → Type
indRectBranchTy ind index T =
  let Ts = ctrArgsTypeList ind index
      k  = ctrRecCount ind index
  in  arrows Ts (arrowRepeat k T T)

-- One method type per constructor of Ind i
indRectBranchTypeList : Nat → Type → List Type
indRectBranchTypeList i T =
  map (λ j → indRectBranchTy i j T) (range (indCtrCount i))
