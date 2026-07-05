{-# OPTIONS --safe #-}

import Definition.Equiv as E
module README (equiv : E.Equiv) where

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

-- Natural numbers and decidability of equality.
import Tools.Nat

-- Lists definition
import Tools.List

-- Proof by reflection for a family of integer inequalities
-- This is used later on to prove that an induction is well-founded:
-- we need to show that the size of the argument decreases with each recursive call
import Tools.Inequality

---------------------------
-- LANGUAGE INTRODUCTION --
---------------------------

-- Syntax and semantics of weakening and substitution.
import Definition.Untyped

-- Propositional equality properties: Equalities between expressions,
-- weakenings, substitutions and their combined composition.
import Definition.Untyped.Properties

-- Judgements: Typing rules, conversion, reduction rules
-- and well-formed substitutions and respective equality.
-- The conversion rule cast-refl is the main contribution of this development.
open import Definition.Typed equiv

-- Well-formed context extraction and reduction properties.
open import Definition.Typed.Properties equiv

-- Well-formed weakening and its properties.
open import Definition.Typed.Weakening equiv


------------------------------
-- KRIPKE LOGICAL RELATIONS --
------------------------------

-- Generic equality relation definition.
open import Definition.Typed.EqualityRelation equiv

-- The judgemental instance of the generic equality.
open import Definition.Typed.EqRelInstance equiv

-- Logical relations definitions.
open import Definition.LogicalRelation equiv

-- Properties of logical relation:

-- Reflexivity of the logical relation.
open import Definition.LogicalRelation.Properties.Reflexivity equiv

-- Escape lemma for the logical relation.
open import Definition.LogicalRelation.Properties.Escape equiv

-- Shape view of two or more types.
open import Definition.LogicalRelation.ShapeView equiv

-- Proof irrelevance for the logical relation.
open import Definition.LogicalRelation.Irrelevance equiv

-- Weakening of logical relation judgements.
open import Definition.LogicalRelation.Weakening equiv

-- Conversion of the logical relation.
open import Definition.LogicalRelation.Properties.Conversion equiv

-- Symmetry of the logical relation.
open import Definition.LogicalRelation.Properties.Symmetry equiv

-- Transitvity of the logical relation.
open import Definition.LogicalRelation.Properties.Transitivity equiv

-- Neutral introduction in the logical relation.
open import Definition.LogicalRelation.Properties.Neutral equiv

-- Weak head expansion of the logical relation.
open import Definition.LogicalRelation.Properties.Reduction equiv

-- Application in the logical relation.
open import Definition.LogicalRelation.Application equiv

-- Validity judgements definitions
open import Definition.LogicalRelation.Substitution equiv

-- Properties of validity judgements:

-- Proof irrelevance for the validity judgements.
open import Definition.LogicalRelation.Substitution.Irrelevance equiv

-- Properties about valid substitutions:
-- * Substitution well-formedness.
-- * Substitution weakening.
-- * Substitution lifting.
-- * Identity substitution.
-- * Reflexivity, symmetry and transitivity of substitution equality.
open import Definition.LogicalRelation.Substitution.Properties equiv

-- Single term substitution of validity judgements.
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst equiv

-- The fundamental theorem.
open import Definition.LogicalRelation.Fundamental equiv

-- Certain cases of the fundamental theorem

-- Validity of the universes
open import Definition.LogicalRelation.Substitution.Introductions.Universe equiv

-- Validity of the empty type and its eliminator
open import Definition.LogicalRelation.Substitution.Introductions.Empty equiv
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec equiv

-- Validity of natural numbers and its eliminator
open import Definition.LogicalRelation.Substitution.Introductions.Nat equiv
open import Definition.LogicalRelation.Substitution.Introductions.Natrec equiv

-- Validity of second natural numbers and its eliminator
open import Definition.LogicalRelation.Substitution.Introductions.Nat2 equiv
open import Definition.LogicalRelation.Substitution.Introductions.Natrec2 equiv

-- Validity of Π-types, abstractions and applications
open import Definition.LogicalRelation.Substitution.Introductions.Pi equiv
open import Definition.LogicalRelation.Substitution.Introductions.Application equiv
open import Definition.LogicalRelation.Substitution.Introductions.Lambda equiv

-- Validity of ∃-types, pairs and projections
open import Definition.LogicalRelation.Substitution.Introductions.Fst equiv
open import Definition.LogicalRelation.Substitution.Introductions.Snd equiv

-- Validity of type casting and proof-irrelevant transport
open import Definition.LogicalRelation.Substitution.Introductions.Castlemmas equiv
open import Definition.LogicalRelation.Substitution.Introductions.Cast equiv
open import Definition.LogicalRelation.Substitution.Introductions.CastPi equiv
open import Definition.LogicalRelation.Substitution.Introductions.Transp equiv

-- Validity of identity types, and reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Id equiv
open import Definition.LogicalRelation.Substitution.Introductions.IdRefl equiv
open import Definition.LogicalRelation.Substitution.Introductions.EquivEq equiv

-- Reducibility of well-formedness.
open import Definition.LogicalRelation.Fundamental.Reducibility equiv

-- Consequences of the fundamental theorem:

-- Consistency (no proof of False in the empty context) implies
-- canonicity of the system.
open import Definition.Typed.Consequences.Canonicity equiv

-- Injectivity of Π-types.
open import Definition.Typed.Consequences.Injectivity equiv

-- Syntactic validitiy of the system.
open import Definition.Typed.Consequences.Syntactic equiv

-- All types and terms fully reduce to WHNF.
open import Definition.Typed.Consequences.Reduction equiv

-- Strong equality of types.
open import Definition.Typed.Consequences.Equality equiv

-- Syntactic inequality of types.
open import Definition.Typed.Consequences.Inequality equiv

-- Substitution in judgements and substitution composition.
open import Definition.Typed.Consequences.Substitution equiv

-- Uniqueness of the types of neutral terms.
open import Definition.Typed.Consequences.NeTypeEq equiv

-- Consistency (0 is not judgementally equal to 1) of the type theory.
open import Definition.Typed.Consequences.Consistency equiv

-- Types can only belong to one universe (because of annotations)
-- also various inequalities for conversion
open import Definition.Typed.Consequences.PiNorm equiv
open import Definition.Typed.Consequences.RelevanceUnicity equiv

-- Terms can only admit one type
open import Definition.Typed.Consequences.TypeUnicity equiv

-- Various inversion results
open import Definition.Typed.Consequences.TypeUnicity equiv

------------------
-- DECIDABILITY --
------------------

-- Conversion algorithm definition.
open import Definition.Conversion equiv

-- A size measure for conversion proofs
-- Because of cast-refl, some proofs cannot be done by structural induction
-- For these, we will show that they terminate by induction on the size of
-- the derivation of algorithmic conversion
open import Definition.Conversion.ConvSize equiv

-----------------------------------------
-- Properties of conversion algorithm: --
-----------------------------------------

-- Context equality and its properties:
-- * Context conversion of typing judgements.
-- * Context conversion of reductions and algorithmic equality.
-- * Reflexivity and symmetry of context equality.
open import Definition.Conversion.Stability equiv

-- Soundness of the conversion algorithm.
open import Definition.Conversion.Soundness equiv

-- Weakening of the conversion algorithm.
open import Definition.Conversion.Weakening equiv

-- The type of the conversion algorithm is stable under definitional equality
open import Definition.Conversion.Conversion equiv

-- Transitivity of the conversion algorithm.
open import Definition.Conversion.Transitivity equiv

-- Symmetry of the conversion algorithm.
open import Definition.Conversion.Symmetry equiv

-- Symmetry does not change the size of the derivation
open import Definition.Conversion.SymmetrySize equiv

-- Conversion is an instance of the generic equality relation interface
open import Definition.Conversion.EqRelInstance equiv

-- Completeness of conversion algorithm.
open import Definition.Conversion.Consequences.Completeness equiv

-- Results around normalisation of reflexive terms
open import Definition.Conversion.FullReduction equiv

-------------------------------------------
-- Decidability of conversion algorithm: --
-------------------------------------------

-- Useful lemmas for the decidability proof
open import Definition.Conversion.HelperDecidable equiv
open import Definition.Conversion.DecidableLemmas equiv
open import Definition.Conversion.DecView equiv

-- Decidability of the conversion algorithm.
open import Definition.Conversion.Decidable equiv

-- Generic equality relation instance for the conversion algorithm.
open import Definition.Conversion.EqRelInstance equiv

-- Decidability of judgemental conversion.
open import Definition.Conversion.HelperDecidable equiv
open import Definition.Typed.Decidable equiv

--------------------------------
-- BONUS: NON-PARANOID TYPING --
--------------------------------

-- The typing rules in Definition.Typed have unnecessary premises
-- Now that we know a lot about the properties of the theory, we can give
-- an alternative and less verbose presentation of the theory
open import Definition.Typed.NonParanoidTyping equiv

-- Likewise, we can do the same for the algorithmic equality, to simplify
-- the conversion checking algorithm
open import Definition.ConversionGen equiv
open import Definition.Conversion.ConversionGenEquiv equiv
