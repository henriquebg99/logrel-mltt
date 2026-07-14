module Definition.SUntyped where

open import Tools.Nat
open import Tools.List


data SType : Set where
  sInd : Nat → SType  -- index for the inductive type
  sArrow : SType → SType → SType

-- Syntax of simple terms
data STerm : Set where
  sVar : Nat → STerm
  sApp : STerm → STerm → STerm
  sLam : SType → STerm → STerm
  sCtr : Nat → Nat → List STerm → STerm
  -- so far no IndRect 
  -- sIndRect : Nat → SType → STerm → List STerm → STerm

postulate sInd_ctr_count : Nat -> Nat
postulate sInd_level : Nat -> Nat
postulate sCtr_args_type_list : Nat → Nat → List SType