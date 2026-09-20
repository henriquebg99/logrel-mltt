import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open import Definition.LogicalRelation.Substitution.Introductions.Application senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Lambda senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Nat senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Natrec senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Empty senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Pi senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst senv equivs public
open import Definition.LogicalRelation.Substitution.Introductions.Universe senv equivs public
