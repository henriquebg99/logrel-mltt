--{-# OPTIONS --safe #-}

-- A Logical Relation for Dependent Type Theory Formalized in Agda
-- Parametrized over a generic equivalence and witnesses that they are reducible in the logical relation.

import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
import Definition.Typed.EqRelInstance as ERI
import Definition.LogicalRelation.EquivRed as ERd

module Everything (equiv : E.Equiv) (equivRed : forall (eqrel : ER.EqRelSet equiv) → ERd.EquivRed equiv {{eqrel = eqrel}}) where

open import Definition.Typed.Decidable equiv equivRed

