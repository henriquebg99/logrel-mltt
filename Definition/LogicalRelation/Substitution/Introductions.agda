import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Application senv swf equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Lambda senv swf equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Empty senv swf equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec senv swf equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Pi senv swf equivs public
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst senv swf equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Universe senv swf equivs public
