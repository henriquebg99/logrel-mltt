{-# OPTIONS --safe #-}

import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Properties (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open import Definition.LogicalRelation.Properties.Reflexivity senv swf equivs public
open import Definition.LogicalRelation.Properties.Symmetry senv swf equivs public
open import Definition.LogicalRelation.Properties.Transitivity senv swf equivs public
open import Definition.LogicalRelation.Properties.Conversion senv swf equivs public
open import Definition.LogicalRelation.Properties.Escape senv swf equivs public
open import Definition.LogicalRelation.Properties.Universe senv swf equivs public
open import Definition.LogicalRelation.Properties.Neutral senv swf equivs public
open import Definition.LogicalRelation.Properties.Reduction senv swf equivs public
open import Definition.LogicalRelation.Properties.MaybeEmb senv swf equivs public
