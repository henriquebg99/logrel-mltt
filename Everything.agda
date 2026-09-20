--{-# OPTIONS --safe #-}

-- A Logical Relation for Dependent Type Theory Formalized in Agda
-- Parametrized over a generic equivalence and witnesses that they are reducible in the logical relation.

import Definition.SUntyped as SI
import Definition.Equiv as E
module Everything (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where

open import Definition.Typed.Decidable senv swf equivs
