{-# OPTIONS --safe #-}

-- A Logical Relation for Dependent Type Theory Formalized in Agda

import Definition.Equiv as E
module Everything (equiv : E.Equiv) where

-- README
open import README equiv

-- Minimal library
open import Tools.Empty
open import Tools.Unit
open import Tools.Nat
open import Tools.Sum
open import Tools.Product
open import Tools.Function
open import Tools.Nullary
open import Tools.List
open import Tools.PropositionalEquality

-- Grammar of the language
open import Definition.Untyped
open import Definition.Untyped.Properties

-- Typing and conversion rules of language
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
open import Definition.Typed.Weakening equiv
open import Definition.Typed.Reduction equiv
open import Definition.Typed.RedSteps equiv
open import Definition.Typed.EqualityRelation equiv
open import Definition.Typed.EqRelInstance equiv

-- Logical relation
open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.ShapeView equiv
open import Definition.LogicalRelation.Irrelevance equiv
open import Definition.LogicalRelation.Weakening equiv
open import Definition.LogicalRelation.Properties equiv
open import Definition.LogicalRelation.Application equiv

open import Definition.LogicalRelation.Substitution equiv
open import Definition.LogicalRelation.Substitution.Properties equiv
open import Definition.LogicalRelation.Substitution.Irrelevance equiv
open import Definition.LogicalRelation.Substitution.Conversion equiv
open import Definition.LogicalRelation.Substitution.Reduction equiv
open import Definition.LogicalRelation.Substitution.Reflexivity equiv
open import Definition.LogicalRelation.Substitution.Weakening equiv
open import Definition.LogicalRelation.Substitution.Reducibility equiv
open import Definition.LogicalRelation.Substitution.Escape equiv
open import Definition.LogicalRelation.Substitution.MaybeEmbed equiv
open import Definition.LogicalRelation.Substitution.Introductions equiv

open import Definition.LogicalRelation.Fundamental equiv
open import Definition.LogicalRelation.Fundamental.Reducibility equiv

-- Consequences of the logical relation for typing and conversion
-- import Definition.Typed.Consequences.Canonicity
open import Definition.Typed.Consequences.Injectivity equiv
open import Definition.Typed.Consequences.Syntactic equiv
open import Definition.Typed.Consequences.Inversion equiv
open import Definition.Typed.Consequences.Inequality equiv
open import Definition.Typed.Consequences.Substitution equiv
open import Definition.Typed.Consequences.Equality equiv
open import Definition.Typed.Consequences.Reduction equiv
open import Definition.Typed.Consequences.NeTypeEq equiv
open import Definition.Typed.Consequences.RelevanceUnicity equiv
open import Definition.Typed.Consequences.SucCong equiv
open import Definition.Typed.Consequences.Consistency equiv

-- Algorithmic equality with lemmas that depend on typing consequences
open import Definition.Conversion equiv
open import Definition.Conversion.Conversion equiv
open import Definition.Conversion.Lift equiv
open import Definition.Conversion.Reduction equiv
open import Definition.Conversion.Soundness equiv
open import Definition.Conversion.Stability equiv
open import Definition.Conversion.Symmetry equiv
open import Definition.Conversion.Transitivity equiv
open import Definition.Conversion.Universe equiv
open import Definition.Conversion.Weakening equiv
open import Definition.Conversion.Whnf equiv
open import Definition.Conversion.EqRelInstance equiv
open import Definition.Conversion.FullReduction equiv

-- Consequences of the logical relation for algorithmic equality
open import Definition.Conversion.Consequences.Completeness equiv

-- Decidability of conversion
open import Definition.Typed.Decidable equiv
open import Definition.Typed.NonParanoidTyping equiv
open import Definition.Conversion.ConversionGenEquiv equiv
open import Definition.Conversion.Decidable equiv
