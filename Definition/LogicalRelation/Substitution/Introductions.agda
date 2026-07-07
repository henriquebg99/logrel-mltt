{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
import Definition.LogicalRelation.EquivRed as ERd
module Definition.LogicalRelation.Substitution.Introductions (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} (equivRed : forall (eqrel : ER.EqRelSet equiv) → ERd.EquivRed equiv eqrel) where
open import Definition.Typed.EqualityRelation equiv

open import Definition.LogicalRelation.Substitution.Introductions.Application equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Lambda equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Nat equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Nat2 equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Natrec equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Empty equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Pi equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst equiv equivRed public
open import Definition.LogicalRelation.Substitution.Introductions.Universe equiv equivRed public
