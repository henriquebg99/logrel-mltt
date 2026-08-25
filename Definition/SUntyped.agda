module Definition.SUntyped where

open import Tools.Nat
open import Tools.List
open import Tools.Nullary using (yes; no)


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

-- all ind levels are 0
-- TODO remove from the deepembedding 0 in sty
postulate indCtrCount : Nat -> Nat
postulate ctrArgsTypeList : Nat → Nat → List Nat -- the type must be an inductive so we only have the index

-- Method type for constructor j of Ind i into non-dependent motive P
-- (Rocq-style: bind each arg; for recursive args also bind an IH : P)
ctrMethodType : Nat → Type → List Nat → Type
ctrMethodType i P [] = P
ctrMethodType i P (a ∷ as) with a ≟ i
... | yes _ = Arrow (Ind a) (Arrow P (ctrMethodType i P as))
... | no  _ = Arrow (Ind a) (ctrMethodType i P as)

-- One method type per constructor of Ind i
indRectMethodTypeList : Nat → Type → List Type
indRectMethodTypeList i P =
  map (λ j → ctrMethodType i P (ctrArgsTypeList i j)) (range (indCtrCount i))
