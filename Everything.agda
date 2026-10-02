{-# OPTIONS --safe #-}

-- A Logical Relation for Dependent Type Theory Formalized in Agda
-- Parametrized over a signature of inductive types and a list of
-- equivalences between them.

module Everything where

-- README
import README

-- Minimal library
import Tools.Empty
import Tools.Unit
import Tools.Nat
import Tools.Sum
import Tools.Product
import Tools.Function
import Tools.Nullary
import Tools.List
import Tools.Maybe
import Tools.Inequality
import Tools.PropositionalEquality

-- Sorts, signature of inductive types and equivalences
import Definition.Sort
import Definition.SUntyped
import Definition.STyped
import Definition.OUntyped
import Definition.OTyped
import Definition.Equiv

-- Grammar of the language
import Definition.Untyped
import Definition.Untyped.Properties
import Definition.Untyped.IndRect

-- Typing and conversion rules of language
import Definition.Typed
import Definition.Typed.Properties
import Definition.Typed.Weakening
import Definition.Typed.Reduction
import Definition.Typed.RedSteps
import Definition.Typed.Embedding
import Definition.Typed.NatExample
import Definition.Typed.IndRectCong
import Definition.Typed.EqualityRelation
import Definition.Typed.EqRelInstance

-- Logical relation
import Definition.LogicalRelation
import Definition.LogicalRelation.ShapeView
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Weakening
import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Application
import Definition.LogicalRelation.EquivRed

import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance
import Definition.LogicalRelation.Substitution.Conversion
import Definition.LogicalRelation.Substitution.Reduction
import Definition.LogicalRelation.Substitution.Reflexivity
import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Reducibility
import Definition.LogicalRelation.Substitution.Escape
import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.ProofIrrelevance
import Definition.LogicalRelation.Substitution.Introductions

import Definition.LogicalRelation.Fundamental
import Definition.LogicalRelation.Fundamental.SimpleTerm
import Definition.LogicalRelation.Fundamental.Reducibility

-- Consequences of the logical relation for typing and conversion
import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.InjectivitySProp
import Definition.Typed.Consequences.Syntactic
import Definition.Typed.Consequences.Inversion
import Definition.Typed.Consequences.Inequality
import Definition.Typed.Consequences.Substitution
import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Reduction
import Definition.Typed.Consequences.NeTypeEq
import Definition.Typed.Consequences.PiNorm
import Definition.Typed.Consequences.RelevanceUnicity
import Definition.Typed.Consequences.TypeUnicity
import Definition.Typed.Consequences.IndRectCong
import Definition.Typed.Consequences.Consistency

-- Algorithmic equality with lemmas that depend on typing consequences
import Definition.Conversion
import Definition.Conversion.ConvSize
import Definition.Conversion.Conversion
import Definition.Conversion.ConversionProp
import Definition.Conversion.Inversion
import Definition.Conversion.Lift
import Definition.Conversion.Reduction
import Definition.Conversion.Soundness
import Definition.Conversion.Stability
import Definition.Conversion.StabilityProp
import Definition.Conversion.Symmetry
import Definition.Conversion.SymmetrySize
import Definition.Conversion.Transitivity
import Definition.Conversion.TransitivityHelper
import Definition.Conversion.Universe
import Definition.Conversion.Weakening
import Definition.Conversion.Whnf
import Definition.Conversion.EqRelInstance
import Definition.Conversion.FullReduction

-- Consequences of the logical relation for algorithmic equality
import Definition.Conversion.Consequences.Completeness

-- Decidability of conversion
import Definition.Conversion.HelperDecidable
import Definition.Conversion.DecidableLemmas
import Definition.Conversion.DecView
import Definition.Conversion.Decidable
import Definition.Typed.Decidable
import Definition.Typed.Consequences.Decidable

-- Non-paranoid typing and generic algorithmic equality
import Definition.Typed.NonParanoidTyping
import Definition.ConversionGen
import Definition.Conversion.WhnfGen
import Definition.Conversion.SoundnessGen
import Definition.Conversion.ConversionGenEquiv
