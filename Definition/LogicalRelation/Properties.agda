import Definition.Typed.EqualityRelation as ER

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.LogicalRelation.Properties (senv : SI.SEnv) (equivs : E.Equivs senv) {{eqrel : ER.EqRelSet senv equivs}} where
open import Definition.Typed.EqualityRelation senv equivs
open import Definition.LogicalRelation.Properties.Reflexivity senv equivs public
open import Definition.LogicalRelation.Properties.Symmetry senv equivs public
open import Definition.LogicalRelation.Properties.Transitivity senv equivs public
open import Definition.LogicalRelation.Properties.Conversion senv equivs public
open import Definition.LogicalRelation.Properties.Escape senv equivs public
open import Definition.LogicalRelation.Properties.Universe senv equivs public
open import Definition.LogicalRelation.Properties.Neutral senv equivs public
open import Definition.LogicalRelation.Properties.Reduction senv equivs public
open import Definition.LogicalRelation.Properties.Successor senv equivs public
open import Definition.LogicalRelation.Properties.MaybeEmb senv equivs public
