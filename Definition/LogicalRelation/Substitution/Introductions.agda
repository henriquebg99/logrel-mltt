{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Substitution.Introductions (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv

open import Definition.LogicalRelation.Substitution.Introductions.Application equiv public
open import Definition.LogicalRelation.Substitution.Introductions.Lambda equiv public
open import Definition.LogicalRelation.Substitution.Introductions.Nat equiv public
open import Definition.LogicalRelation.Substitution.Introductions.Natrec equiv public
open import Definition.LogicalRelation.Substitution.Introductions.Empty equiv public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec equiv public
open import Definition.LogicalRelation.Substitution.Introductions.Pi equiv public
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst equiv public
open import Definition.LogicalRelation.Substitution.Introductions.Universe equiv public
