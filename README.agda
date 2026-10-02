{-# OPTIONS --safe #-}

module README where

-- Formalization of the decidability of conversion for a fragment of CICobs
-- Git repository: https://github.com/CoqHott/logrel-mltt/tree/impredicativity-cast-compute-refl
-- DOI of this artifact: 10.5281/zenodo.10499152

------------------
-- INTRODUCTION --
------------------

-- A minimal library necessary for formalization:

-- The empty type and its elimination rule.
import Tools.Empty

-- The unit type.
import Tools.Unit

-- Disjoint sum type.
import Tools.Sum

-- Products and Sigma-types.
import Tools.Product

-- Identity function and composition.
import Tools.Function

-- Negation and decidability type.
import Tools.Nullary

-- Propositional equality and its properties.
import Tools.PropositionalEquality

-- Decidability of equality.
import Tools.Nat

-- Lists definition
import Tools.List

-- Maybe type.
import Tools.Maybe

-- Proof by reflection for a family of integer inequalities
-- This is used later on to prove that an induction is well-founded:
-- we need to show that the size of the argument decreases with each recursive call
import Tools.Inequality

---------------------------
-- LANGUAGE INTRODUCTION --
---------------------------

-- Sorts of types (relevance and level) and typing contexts.
import Definition.Sort

-- Signature of the inductive types: the simple types of the arguments of
-- their constructors, and positivity. The development is parameterized by
-- a signature [senv] and a proof [swf] that it is well formed.
import Definition.SUntyped

-- Typing of simple terms (variables, lambdas, applications, constructors
-- and eliminators of inductive types).
import Definition.STyped

-- Terms without equivalence witnesses, and their typing rules.
-- They are used to state the types of the proofs of the equivalences.
import Definition.OUntyped
import Definition.OTyped

-- Equivalences between inductive types. The development is parameterized
-- by a list [equivs] of such equivalences.
import Definition.Equiv

-- Syntax and semantics of weakening and substitution.
import Definition.Untyped

-- Propositional equality properties: Equalities between expressions,
-- weakenings, substitutions and their combined composition.
import Definition.Untyped.Properties

-- Normal form of the types of the methods of the eliminator IndRect.
import Definition.Untyped.IndRect

-- Judgements: Typing rules, conversion, reduction rules
-- and well-formed substitutions and respective equality.
-- The conversion rule cast-refl is the main contribution of this development.
import Definition.Typed

-- Well-formed context extraction and reduction properties.
import Definition.Typed.Properties

-- Well-formed weakening and its properties.
import Definition.Typed.Weakening

-- Embedding of the typing of terms without equivalence witnesses.
import Definition.Typed.Embedding

-- Natural numbers as an instance of the inductive types.
import Definition.Typed.NatExample

------------------------------
-- KRIPKE LOGICAL RELATIONS --
------------------------------

-- Generic equality relation definition.
import Definition.Typed.EqualityRelation

-- The judgemental instance of the generic equality.
import Definition.Typed.EqRelInstance

-- Logical relations definitions.
import Definition.LogicalRelation

-- Properties of logical relation:

-- Reflexivity of the logical relation.
import Definition.LogicalRelation.Properties.Reflexivity

-- Escape lemma for the logical relation.
import Definition.LogicalRelation.Properties.Escape

-- Shape view of two or more types.
import Definition.LogicalRelation.ShapeView

-- Proof irrelevance for the logical relation.
import Definition.LogicalRelation.Irrelevance

-- Weakening of logical relation judgements.
import Definition.LogicalRelation.Weakening

-- Conversion of the logical relation.
import Definition.LogicalRelation.Properties.Conversion

-- Symmetry of the logical relation.
import Definition.LogicalRelation.Properties.Symmetry

-- Transitvity of the logical relation.
import Definition.LogicalRelation.Properties.Transitivity

-- Neutral introduction in the logical relation.
import Definition.LogicalRelation.Properties.Neutral

-- Weak head expansion of the logical relation.
import Definition.LogicalRelation.Properties.Reduction

-- Application in the logical relation.
import Definition.LogicalRelation.Application

-- Reducibility of the functions of the equivalences, needed by the cast rules.
import Definition.LogicalRelation.EquivRed

-- Validity judgements definitions
import Definition.LogicalRelation.Substitution

-- Properties of validity judgements:

-- Proof irrelevance for the validity judgements.
import Definition.LogicalRelation.Substitution.Irrelevance

-- Properties about valid substitutions:
-- * Substitution well-formedness.
-- * Substitution weakening.
-- * Substitution lifting.
-- * Identity substitution.
-- * Reflexivity, symmetry and transitivity of substitution equality.
import Definition.LogicalRelation.Substitution.Properties

-- Single term substitution of validity judgements.
import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

-- The fundamental theorem.
import Definition.LogicalRelation.Fundamental
-- Certain cases of the fundamental theorem

-- Validity of the universes
import Definition.LogicalRelation.Substitution.Introductions.Universe

-- Validity of inductive types, their constructors and their eliminator
import Definition.Typed.IndRectCong
import Definition.LogicalRelation.Substitution.Introductions.Ind
import Definition.LogicalRelation.Substitution.Introductions.IndRectBranch
import Definition.LogicalRelation.Substitution.Introductions.IndRect

-- Validity of the empty type and its eliminator
import Definition.LogicalRelation.Substitution.Introductions.Empty
import Definition.LogicalRelation.Substitution.Introductions.Emptyrec

-- Validity of Π-types, abstractions and applications
import Definition.LogicalRelation.Substitution.Introductions.Pi
import Definition.LogicalRelation.Substitution.Introductions.Application
import Definition.LogicalRelation.Substitution.Introductions.Lambda

-- Validity of ∃-types, pairs and projections
import Definition.LogicalRelation.Substitution.Introductions.Fst
import Definition.LogicalRelation.Substitution.Introductions.Snd

-- Validity of type casting and proof-irrelevant transport
import Definition.LogicalRelation.Substitution.Introductions.Castlemmas
import Definition.LogicalRelation.Substitution.Introductions.Cast
import Definition.LogicalRelation.Substitution.Introductions.CastPi
import Definition.LogicalRelation.Substitution.Introductions.CastRefl
import Definition.LogicalRelation.Substitution.Introductions.Transp

-- Validity of identity types, and reflexivity
import Definition.LogicalRelation.Substitution.Introductions.Id
import Definition.LogicalRelation.Substitution.Introductions.IdRefl
import Definition.LogicalRelation.Substitution.Introductions.EquivEq

-- Validity of simple terms, and reducibility of the functions of the equivalences.
import Definition.LogicalRelation.Fundamental.SimpleTerm

-- Reducibility of well-formedness.
import Definition.LogicalRelation.Fundamental.Reducibility
-- Consequences of the fundamental theorem:

-- Injectivity of Π-types.
import Definition.Typed.Consequences.Injectivity

-- Syntactic validitiy of the system.
import Definition.Typed.Consequences.Syntactic

-- All types and terms fully reduce to WHNF.
import Definition.Typed.Consequences.Reduction

-- Strong equality of types.
import Definition.Typed.Consequences.Equality

-- Syntactic inequality of types.
import Definition.Typed.Consequences.Inequality

-- Substitution in judgements and substitution composition.
import Definition.Typed.Consequences.Substitution

-- Uniqueness of the types of neutral terms.
import Definition.Typed.Consequences.NeTypeEq

-- Distinct constructors are not judgmentally equal.
import Definition.Typed.Consequences.Consistency

-- Congruence of the types of the methods of IndRect.
import Definition.Typed.Consequences.IndRectCong

-- Types can only belong to one universe (because of annotations)
-- also various inequalities for conversion
import Definition.Typed.Consequences.PiNorm
import Definition.Typed.Consequences.RelevanceUnicity

-- Terms can only admit one type, various inversion results
import Definition.Typed.Consequences.TypeUnicity

------------------
-- DECIDABILITY --
------------------

-- Conversion algorithm definition.
import Definition.Conversion

-- A size measure for conversion proofs
-- Because of cast-refl, some proofs cannot be done by structural induction
-- For these, we will show that they terminate by induction on the size of
-- the derivation of algorithmic conversion
import Definition.Conversion.ConvSize

-----------------------------------------
-- Properties of conversion algorithm: --
-----------------------------------------

-- Context equality and its properties:
-- * Context conversion of typing judgements.
-- * Context conversion of reductions and algorithmic equality.
-- * Reflexivity and symmetry of context equality.
import Definition.Conversion.Stability

-- Soundness of the conversion algorithm.
import Definition.Conversion.Soundness

-- Weakening of the conversion algorithm.
import Definition.Conversion.Weakening

-- The type of the conversion algorithm is stable under definitional equality
import Definition.Conversion.Conversion

-- Transitivity of the conversion algorithm.
import Definition.Conversion.Transitivity

-- Symmetry of the conversion algorithm.
import Definition.Conversion.Symmetry

-- Symmetry does not change the size of the derivation
import Definition.Conversion.SymmetrySize

-- Conversion is an instance of the generic equality relation interface
import Definition.Conversion.EqRelInstance

-- Completeness of conversion algorithm.
import Definition.Conversion.Consequences.Completeness

-- Results around normalisation of reflexive terms
import Definition.Conversion.FullReduction

-------------------------------------------
-- Decidability of conversion algorithm: --
-------------------------------------------

-- Useful lemmas for the decidability proof
import Definition.Conversion.HelperDecidable
import Definition.Conversion.DecidableLemmas
import Definition.Conversion.DecView

-- Decidability of the conversion algorithm.
import Definition.Conversion.Decidable

-- Generic equality relation instance for the conversion algorithm.
import Definition.Conversion.EqRelInstance

-- Decidability of judgemental conversion.
import Definition.Conversion.HelperDecidable
import Definition.Typed.Decidable

--------------------------------
-- BONUS: NON-PARANOID TYPING --
--------------------------------

-- The typing rules in Definition.Typed have unnecessary premises
-- Now that we know a lot about the properties of the theory, we can give
-- an alternative and less verbose presentation of the theory
import Definition.Typed.NonParanoidTyping

-- Likewise, we can do the same for the algorithmic equality, to simplify
-- the conversion checking algorithm
import Definition.ConversionGen
import Definition.Conversion.ConversionGenEquiv