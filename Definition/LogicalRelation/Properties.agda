{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Properties (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv


open import Definition.LogicalRelation.Properties.Reflexivity equiv public
open import Definition.LogicalRelation.Properties.Symmetry equiv public
open import Definition.LogicalRelation.Properties.Transitivity equiv public
open import Definition.LogicalRelation.Properties.Conversion equiv public
open import Definition.LogicalRelation.Properties.Escape equiv public
open import Definition.LogicalRelation.Properties.Universe equiv public
open import Definition.LogicalRelation.Properties.Neutral equiv public
open import Definition.LogicalRelation.Properties.Reduction equiv public
open import Definition.LogicalRelation.Properties.Successor equiv public
open import Definition.LogicalRelation.Properties.MaybeEmb equiv public
