-- Algorithmic equality.

{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.ConversionGen (senv : SI.SEnv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
import Definition.SUntyped as SU
open import Definition.Typed senv equivs
open import Tools.Nat
open import Tools.Product
open import Tools.List using (List; All₃; map; _∈ₗ_)
open import Tools.Maybe using (just)
import Tools.PropositionalEquality as PE
infix 10 _⊢⊢_~_↑_^_
infix 10 _⊢⊢_[conv↑]_^_
infix 10 _⊢⊢_[conv↓]_^_
infix 10 _⊢⊢_[conv↑]_∷_^_
infix 10 _⊢⊢_[conv↓]_∷_^_
infix 10 _⊢⊢_[genconv↑]_∷_^_

data PosType : Term → Set where
  Indₙ : ∀ {i} → PosType (Ind i)
  Uₙ : ∀ {r l} → PosType (Univ r l)
  ne : ∀{n} → Neutral n → PosType n

-- These views classify only whnfs.
-- PosType and Function are subsets of Whnf.

posTypeWhnf : ∀ {A} → PosType A → Whnf A
posTypeWhnf Indₙ = Indₙ
posTypeWhnf Uₙ  = Uₙ
posTypeWhnf (ne x) = ne x

mutual
  -- Neutral equality.
  data _⊢⊢_~_↑!_^_ (Γ : Con Term) : (k l A : Term) → TypeLevel → Set where
    var-refl    : ∀ {x y A l}
                → Γ ⊢ var x ∷ A ^ [ ! , l ]
                → x PE.≡ y
                → Γ ⊢⊢ var x ~ var y ↑! A ^ l
    app-cong    : ∀ {k l t v F rF lF lG G lΠ}
                → Γ ⊢⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ
                → Γ ⊢⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ]
                → Γ ⊢⊢ k ∘ t ^ lΠ ~ l ∘ v ^ lΠ ↑! G [ t ] ^ ι lG
    IndRect-cong : ∀ {ind P P' t t' ms ms' lG}
                → ind ∈ₗ senv
                → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢⊢ P [conv↑] P' ^ [ ! , ι lG ]
                → Γ ⊢⊢ t ~ t' ↓! Ind (SU.SInd.name ind) ^ ι ⁰
                → All₃ (λ m m' A → Γ ⊢⊢ m [conv↑] m' ∷ A ^ ι lG) ms ms' (indRectBranchTyList ind P ! lG)
                → Γ ⊢⊢ IndRect (SU.SInd.name ind) lG P t ms ~ IndRect (SU.SInd.name ind) lG P' t' ms'
                      ↑! (P [ t ]) ^ ι lG
    Emptyrec-cong : ∀ {k l F G ll}
                  → Γ ⊢⊢ F [conv↑] G ^ [ ! , ι ll ]
                  → Γ ⊢⊢ k ~ l ↑% sEmpty ^ ι ⁰
                  → Γ ⊢⊢ Emptyrec ll ⁰ F k ~ Emptyrec ll ⁰ G l ↑! F ^ ι ll
    cast-cong : ∀ {A A' B B' t t' e e'}
              → Γ ⊢⊢ A [conv↓] A' ∷ U ⁰ ^ next ⁰
              → Γ ⊢⊢ B' [conv↓] B ∷ U ⁰ ^ ι ¹
              → Γ ⊢⊢ t [conv↑] t' ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , ι ⁰ ]
              → Neutral (cast ⁰ A B e t)
              → Neutral (cast ⁰ A' B' e' t')             
              → Γ ⊢⊢ cast ⁰ A B e t ~ cast ⁰ A' B' e' t' ↑! B ^ ι ⁰
    cast-refl : ∀ {A B t u e}
              → Γ ⊢⊢ A [conv↓] B ∷ U ⁰ ^ next ⁰
              → Γ ⊢⊢ t [conv↓] u ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
              → Neutral (cast ⁰ A B e t)
              → Neutral u
              → Γ ⊢⊢ cast ⁰ A B e t ~ u ↑! B ^ ι ⁰
    cast-refl' : ∀ {A B t u e}
              → Γ ⊢⊢ B [conv↓] A ∷ U ⁰ ^ next ⁰
              → Γ ⊢⊢ t [conv↓] u ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
              → Neutral (cast ⁰ A B e u)
              → Neutral t
              → Γ ⊢⊢ t ~ cast ⁰ A B e u ↑! A ^ ι ⁰

  record _⊢⊢_~_↑%_^_ (Γ : Con Term) (k l A : Term) (ll : TypeLevel) : Set where
    inductive
    constructor %~↑
    field
      ⊢⊢k : Γ ⊢ k ∷ A ^ [ % , ll ]
      ⊢⊢l : Γ ⊢ l ∷ A ^ [ % , ll ]

  data _⊢⊢_~_↑_^_ (Γ : Con Term) : (k l A : Term) → TypeInfo → Set where
    ~↑! : ∀ {k l A ll} → Γ ⊢⊢ k ~ l ↑! A ^ ll → Γ ⊢⊢ k ~ l ↑ A ^ [ ! , ll ]
    ~↑% : ∀ {k l A ll} → Γ ⊢⊢ k ~ l ↑% A ^ ll → Γ ⊢⊢ k ~ l ↑ A ^ [ % , ll ]

  -- Neutral equality with types in WHNF.
  record _⊢⊢_~_↓!_^_ (Γ : Con Term) (k l B : Term) (ll : TypeLevel) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B ^ [ ! , ll ]
      whnfB : Whnf B
      k~l   : Γ ⊢⊢ k ~ l ↑! A ^ ll

  -- Type equality.
  record _⊢⊢_[conv↑]_^_ (Γ : Con Term) (A B : Term) (rA : TypeInfo) : Set where
    inductive
    constructor [↑]
    field
      A′ B′  : Term
      D      : Γ ⊢ A ⇒* A′ ^ rA
      D′     : Γ ⊢ B ⇒* B′ ^ rA
      whnfA′ : Whnf A′
      whnfB′ : Whnf B′
      A′<>B′ : Γ ⊢⊢ A′ [conv↓] B′ ^ rA

  -- Type equality with types in WHNF.
  data _⊢⊢_[conv↓]_^_ (Γ : Con Term) : (A B : Term) → TypeInfo → Set where
    U-refl    : ∀ {r r' }
              → r PE.≡ r' -- needed for K issues
              → ⊢ Γ → Γ ⊢⊢ Univ r ¹ [conv↓] Univ r' ¹ ^ [ ! , next ¹ ]
    univ      : ∀ {A B r l}
              → Γ ⊢⊢ A [conv↓] B ∷ Univ r l ^ next l
              → Γ ⊢⊢ A [conv↓] B ^ [ r , ι l ]

  -- Term equality.
  record _⊢⊢_[conv↑]_∷_^_ (Γ : Con Term) (t u A : Term) (l : TypeLevel) : Set where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term
      D       : Γ ⊢ A ⇒* B ^ [ ! , l ]
      d       : Γ ⊢ t ⇒* t′ ∷ B ^ l
      d′      : Γ ⊢ u ⇒* u′ ∷ B ^ l
      whnfB   : Whnf B
      whnft′  : Whnf t′
      whnfu′  : Whnf u′
      t<>u    : Γ ⊢⊢ t′ [conv↓] u′ ∷ B ^ l

  -- Term equality with types and terms in WHNF.
  data _⊢⊢_[conv↓]_∷_^_ (Γ : Con Term) : (t u A : Term) (l : TypeLevel) → Set where
    U-cong    : ∀ {r r' }
              → r PE.≡ r' -- needed for K issues
              → ⊢ Γ → Γ ⊢⊢ Univ r ⁰ [conv↓] Univ r' ⁰ ∷ U ¹ ^ next ¹
    Ind-cong  : ∀ {i} → ⊢ Γ → i ∈ₗ SU.indNames senv → Γ ⊢⊢ Ind i [conv↓] Ind i ∷ U ⁰ ^ next ⁰
    Empty-cong : ⊢ Γ → Γ ⊢⊢ sEmpty [conv↓] sEmpty ∷ SProp ^ next ⁰
    Π-cong    : ∀ {F G H E rF rH rΠ lF lH lG lE lΠ ll}
              → ll PE.≡ next lΠ
              → rF PE.≡ rH -- needed for K issues
              → lF PE.≡ lH -- needed for K issues
              → lG PE.≡ lE -- needed for K issues
              → (rΠ PE.≡ ! → lF ≤ lΠ × lG ≤ lΠ)
              → (rΠ PE.≡ % → lG PE.≡ ⁰ × lΠ PE.≡ ⁰)
              → Γ ⊢⊢ F [conv↑] H ∷ Univ rF lF ^ next lF
              → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G [conv↑] E  ∷ Univ rΠ lG ^ next lG
              → Γ ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ rΠ [conv↓] Π H ^ rH ° lH ▹ E ° lE ° lΠ ^ rΠ ∷ Univ rΠ lΠ ^ ll
    Id-cong : ∀ {l A A' t t' u u'}
              → Γ ⊢⊢ A [conv↑] A' ∷ U l ^ next l
              → Γ ⊢⊢ t [conv↑] t' ∷ A ^ ι l
              → Γ ⊢⊢ u [conv↑] u' ∷ A ^ ι l
              → Γ ⊢⊢ Id A t u [conv↓] Id A' t' u' ∷ SProp ^ next ⁰
    ctr-cong  : ∀ {ind j args args' Ts}
              → ⊢ Γ
              → ind ∈ₗ senv
              → SU.ctrArgsTypeList ind j PE.≡ just Ts
              → All₃ (λ a a' A → Γ ⊢⊢ a [conv↑] a' ∷ A ^ ι ⁰) args args' (map emb-stype Ts)
              → Γ ⊢⊢ ctr (SU.SInd.name ind) j args [conv↓] ctr (SU.SInd.name ind) j args'
                    ∷ Ind (SU.SInd.name ind) ^ ι ⁰
    ne        : ∀ {k l M W ll}
              → Γ ⊢ k ∷ W ^ [ ! , ll ]
              → Γ ⊢ l ∷ W ^ [ ! , ll ]
              → PosType W
              → Γ ⊢⊢ k ~ l ↓! M ^ ll
              → Γ ⊢⊢ k [conv↓] l ∷ W ^ ll
{-    lam-cong  : ∀ {t t' F F' G rF lF lG l}
              → lF ≤ l
              → lG ≤ l
              → Γ ⊢ lam F' ▹ t' ^ l ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
              → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ t [conv↑] t' ∷ G ^ ι lG
              → Γ ⊢⊢ lam F ▹ t ^ l [conv↓] lam F' ▹ t' ^ l ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ ι l-}
    η-eq      : ∀ {f g F G rF lF lG l}
              → lF ≤ l
              → lG ≤ l
              → Γ ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
              → Γ ⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
              → Function f
              → Function g
              → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ wk1 f ∘ var 0 ^ l [conv↑] wk1 g ∘ var 0 ^ l ∷ G ^ ι lG
              → Γ ⊢⊢ f [conv↓] g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ ι l

  _⊢⊢_[genconv↑]_∷_^_ : (Γ : Con Term) (t u A : Term) (r : TypeInfo) → Set
  _⊢⊢_[genconv↑]_∷_^_ Γ k l A [ ! , ll ] =  Γ ⊢⊢ k [conv↑] l ∷ A ^ ll
  _⊢⊢_[genconv↑]_∷_^_ Γ k l A [ % , ll ] =  Γ ⊢⊢ k ~ l ↑% A ^  ll
