module Definition.SUntyped where

open import Tools.Nat
open import Tools.List


data Type : Set where
  Ind : Nat → Type  -- index for the inductive type
  Arrow : Type → Type → Type

-- Syntax of simple terms
data Term : Set where
  var : Nat → Term
  app : Term → Term → Term
  lam : Type → Term → Term
  ctr : Nat → Nat → List Term → Term
  -- so far no IndRect 
  -- IndRect : Nat → Type → Term → List Term → Term

-- all ind levels are 0 
-- TODO remove from the deepembedding 0 in sty
postulate indCtrCount : Nat -> Nat
postulate ctrArgsTypeList : Nat → Nat → List Type