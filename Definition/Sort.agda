-- Sorts (level and relevance) of types.
-- Contexts Con
module Definition.Sort where
open import Tools.Nat
open import Tools.Product
open import Tools.List
import Tools.PropositionalEquality as PE
infixl 30 _∙_^_

data Relevance : Set where
  ! : Relevance -- proof-relevant
  % : Relevance -- proof-irrelevant

!≢% : ! PE.≢ %
!≢% ()

-- two levels of small types
data Level : Set where
  ⁰ : Level
  ¹ : Level

⁰≢¹ : ⁰ PE.≢ ¹
⁰≢¹ ()

data _<_ : (i j : Level) → Set where
  0<1 : ⁰ < ¹

data _≤_ (i j : Level) : Set where
  <is≤  : i < j → i ≤ j
  ≡is≤ : i PE.≡ j → i ≤ j

-- Large type levels : ι ⁰, ι ¹, ∞
data TypeLevel : Set where
  ι : Level → TypeLevel
  ∞ : TypeLevel

data _<∞_ : (i j : TypeLevel) → Set where
  emb< : ι ⁰ <∞ ι ¹
  ∞< : ι ¹ <∞ ∞
  -- ∞<⁰ : ι ⁰ <∞ ∞

data _≤∞_ (i j : TypeLevel) : Set where
  <∞is≤∞  : i <∞ j → i ≤∞ j
  ≡is≤∞ : i PE.≡ j → i ≤∞ j

next : Level → TypeLevel
next ⁰ = ι ¹
next ¹ = ∞

toLevel : TypeLevel → Level
toLevel (ι ⁰) = ⁰
toLevel (ι ¹) = ¹
toLevel ∞ = ¹

predLevel : TypeLevel → Level
predLevel (ι ⁰) = ⁰
predLevel (ι ¹) = ⁰
predLevel ∞ = ¹

maxLevel : (i : Level) → (j : Level) → Σ Level λ k → i ≤ k × j ≤ k
maxLevel ⁰ ⁰ = ⁰ , ((≡is≤ PE.refl) , (≡is≤ PE.refl))
maxLevel ⁰ ¹ = ¹ , ((<is≤ 0<1) , (≡is≤ PE.refl))
maxLevel ¹ ⁰ = ¹ , ((≡is≤ PE.refl) , (<is≤ 0<1))
maxLevel ¹ ¹ = ¹ , ((≡is≤ PE.refl) , (≡is≤ PE.refl))

⁰min : (i : Level) → ⁰ ≤ i
⁰min ⁰ = ≡is≤ PE.refl
⁰min ¹ = <is≤ 0<1

<next : ∀ {l} → ι l <∞ next l
<next {⁰} = emb<
<next {¹} = ∞<

levelBounded : (i : Level) → Σ TypeLevel λ k → ι i <∞ k
levelBounded i = next i , <next

ιinj : ∀ {l l'} → ι l PE.≡ ι l' → l PE.≡ l'
ιinj {⁰} {⁰} e = PE.refl
ιinj {¹} {¹} e = PE.refl

next-inj : ∀ {l l'} → next l PE.≡ next l' → l PE.≡ l'
next-inj {⁰} {⁰} e = PE.refl
next-inj {¹} {¹} e = PE.refl

-- In a typing judgment, a type is generally annotated with a pair of a relevance and a level
record TypeInfo : Set where
  constructor [_,_]
  field
    r : Relevance
    l : TypeLevel

toTypeInfo : Relevance × Level → TypeInfo
toTypeInfo ( r , l ) = [ r , ι l ]

-- Typing contexts (snoc-lists, isomorphic to lists).
data Con (A : Set) : Set where
  ε   : Con A               -- Empty context.
  _∙_^_ : Con A → A → TypeInfo → Con A  -- Context extension.

record GenT (A : Set) : Set where
  inductive
  constructor ⟦_,_⟧
  field
    l : Nat
    t : A