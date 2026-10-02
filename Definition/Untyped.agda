-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Untyped (senv : SI.SEnv) (equivs : E.Equivs senv) where

open import Tools.Nat
open import Tools.Product
open import Tools.List
open import Tools.Inequality using (filter; true; false)
open import Tools.Nullary using (yes; no)
import Tools.PropositionalEquality as PE
open import Definition.Sort public
import Definition.OUntyped senv as O
import Definition.Equiv senv as Eq
import Definition.SUntyped as SU
OTerm = O.Term
OKind = O.Kind

infix 30 Π_^_°_▹_°_°_^_
infixr 22 _^_°_▹▹_°_°_^_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑
infix 25 _[_]↑^_

data Kind : Set where
  Ukind : Relevance → Level → Kind
  Indkind : Nat → Kind
  Pikind : Relevance → Level → Level → Level → Relevance → Kind
  Lamkind : Level → Kind
  Appkind : Level → Kind
  Emptykind : Level → Kind
  Emptyreckind : Level → Level → Kind
  Idkind : Kind
  Idreflkind : Kind
  Idpikind : Kind
  Idspropkind : Kind
  Transpkind : Kind
  Castkind : Level → Kind
  Castreflkind : Kind
  Fstkind : Kind
  Sndkind : Kind
  Equivkind : Nat → Kind -- Equivalence witness
  Ctrkind : Nat → Nat → Kind -- index of inductive type, index of constructor
  IndRectkind : Nat → Level → Kind -- inductive eliminator (motive level)

data Term : Set where
  var : (x : Nat) → Term
  gen : (k : Kind) (c : List (GenT Term)) → Term

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.

-- Type constructors.
-- Universes of proof-relevant types
U      : Level → Term
U l = gen (Ukind ! l) []

-- Universes of proof-irrelevant types
SProp : Term
SProp = gen (Ukind % ⁰) []

pattern Univ r l = gen (Ukind r l) []

-- Dependent product, with level annotations for the domain, codomain, and resulting type
Π_^_°_▹_°_°_^_   : Term → Relevance → Level → Term → Level → Level → Relevance → Term  -- Dependent function type (B is a binder).
Π A ^ r ° lA ▹ B ° lB ° lΠ ^ rΠ = gen (Pikind r lA lB lΠ rΠ) (⟦ 0 , A ⟧ ∷ ⟦ 1 , B ⟧ ∷ [])

-- Lambda-calculus.
-- var    : (x : Nat)        → Term  -- Variable (de Bruijn index).
-- var = var

lam_▹_^_    : Term → Term → Level → Term  -- Function abstraction (binder).
lam A ▹ t ^ l = gen (Lamkind l) (⟦ 0 , A ⟧ ∷ ⟦ 1 , t ⟧ ∷ [])

_∘_^_    : (t u : Term) (l : Level)    → Term  -- Application.
t ∘ u ^ l = gen (Appkind l) (⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

fst : (t : Term) → Term -- Dependent pair elimination
fst t = gen Fstkind (⟦ 0 , t ⟧ ∷ [])

snd : (t : Term) → Term -- Dependent pair elimination
snd t = gen Sndkind (⟦ 0 , t ⟧ ∷ [])

-- Empty type
Empty : Level → Term
Empty l = gen (Emptykind l) []

sEmpty : Term
sEmpty = Empty ⁰

-- Eliminator for the empty type
Emptyrec : (l lEmpty : Level) (A e : Term) -> Term
Emptyrec l lEmpty A e = gen (Emptyreckind l lEmpty) (⟦ 0 , A ⟧ ∷ ⟦ 0 , e ⟧ ∷ [])

-- Identity type
Id : (A t u : Term) → Term
Id A t u = gen Idkind (⟦ 0 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

-- witness of reflexivity of equality
Idrefl : (A t : Term) → Term
Idrefl A t = gen Idreflkind (⟦ 0 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ [])

-- witness of functional extensionality
IdΠ : (A B t u : Term) → Term
IdΠ A B t u = gen Idpikind (⟦ 0 , A ⟧ ∷ ⟦ 0 , B ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

-- witness of functional extensionality
IdSProp : (A B : Term) → Term
IdSProp A B = gen Idspropkind (⟦ 0 , A ⟧ ∷ ⟦ 0 , B ⟧ ∷ [])

-- transport on propositions
transp : (A P t s u e : Term) → Term
transp A P t s u e = gen Transpkind (⟦ 0 , A ⟧ ∷ ⟦ 1 , P ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , s ⟧ ∷ ⟦ 0 , u ⟧ ∷ ⟦ 0 , e ⟧ ∷ [])

-- cast between types, used to implement transport
cast : Level → (A B e t : Term) → Term
cast l A B e t = gen (Castkind l) (⟦ 0 , A ⟧ ∷ ⟦ 0 , B ⟧ ∷ ⟦ 0 , e ⟧ ∷ ⟦ 0 , t ⟧ ∷ [])

-- propositional proof that casting with reflexivity is the identity
castrefl : (A t : Term) → Term
castrefl A t = gen Castreflkind (⟦ 0 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ [])

-- Equivalence witness
equiv-eq : Nat → Term
equiv-eq i = gen (Equivkind i) []

-- inductive type
Ind : Nat → Term
Ind i = gen (Indkind i) []

-- constructor
ctr : Nat → Nat → List Term → Term
ctr i j ts = gen (Ctrkind i j) (map (λ t → ⟦ 0 , t ⟧) ts)

-- inductive eliminator (P is a type family over Ind i, so a binder)
IndRect : Nat → Level → Term → Term → List Term → Term
IndRect i lG P t ms = gen (IndRectkind i lG) (⟦ 1 , P ⟧ ∷ ⟦ 0 , t ⟧ ∷ map (λ m → ⟦ 0 , m ⟧) ms)

------------------------------------------------------------------------
-- Embedding of OTerms into Terms

emb-okind : OKind → Kind
emb-okind (O.Ukind r l) = Ukind r l
emb-okind (O.Indkind i) = Indkind i
emb-okind (O.Pikind r lA lB lΠ rΠ) = Pikind r lA lB lΠ rΠ
emb-okind (O.Lamkind l) = Lamkind l
emb-okind (O.Appkind l) = Appkind l
emb-okind (O.Emptykind l) = Emptykind l
emb-okind (O.Emptyreckind l lEmpty) = Emptyreckind l lEmpty
emb-okind O.Idkind = Idkind
emb-okind O.Idreflkind = Idreflkind
emb-okind O.Idpikind = Idpikind
emb-okind O.Idspropkind = Idspropkind
emb-okind O.Transpkind = Transpkind
emb-okind (O.Castkind l) = Castkind l
emb-okind O.Castreflkind = Castreflkind
emb-okind O.Fstkind = Fstkind
emb-okind O.Sndkind = Sndkind
emb-okind (O.Ctrkind i j) = Ctrkind i j
emb-okind (O.IndRectkind i l) = IndRectkind i l

mutual
  emb-otermGen : List (GenT OTerm) → List (GenT Term)
  emb-otermGen [] = []
  emb-otermGen (⟦ l , t ⟧ ∷ gs) = ⟦ l , emb-oterm t ⟧ ∷ emb-otermGen gs

  emb-oterm : OTerm → Term
  emb-oterm (O.var x) = var x
  emb-oterm (O.gen k gs) = gen (emb-okind k) (emb-otermGen gs)

emb-con : Con OTerm → Con Term
emb-con ε = ε
emb-con (Γ ∙ A ^ r) = emb-con Γ ∙ emb-oterm A ^ r

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  Π F G = Π H E  then  F = H  and  G = E.

Π-PE-injectivity : ∀ {F rF lF G lG lΠ r H rH lH E lE lΠ' r'} → Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r PE.≡ Π H ^ rH ° lH ▹ E ° lE ° lΠ' ^ r'
  → F PE.≡ H × rF PE.≡ rH × lF PE.≡ lH × G PE.≡ E × lG PE.≡ lE × lΠ PE.≡ lΠ' × r PE.≡ r'
Π-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

Id-PE-injectivity : ∀ {F G t u t' u'} → Id F t u PE.≡ Id G t' u'
  → F PE.≡ G × t PE.≡ t' × u PE.≡ u'
Id-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- If  cast l A B e t = cast l' A' B' e' t'  then all the arguments are equal.

cast-PE-injectivity : ∀ {A A' B B' e e' t t' l l'} → cast l A B e t PE.≡ cast l' A' B' e' t'
  → l PE.≡ l' × A PE.≡ A' × B PE.≡ B' × e PE.≡ e' × t PE.≡ t'
cast-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

gen-PE-injectivity : ∀ {k k' ts ts'} → gen k ts PE.≡ gen k' ts' → k PE.≡ k' × ts PE.≡ ts'
gen-PE-injectivity PE.refl = PE.refl , PE.refl

GenT-PE-injectivity : ∀ {A : Set} {n n'} {t t' : A} → ⟦ n , t ⟧ PE.≡ ⟦ n' , t' ⟧ → n PE.≡ n' × t PE.≡ t'
GenT-PE-injectivity PE.refl = PE.refl , PE.refl

ctr-PE-injectivity : ∀ {i i' j j' ts ts'} →
  ctr i j ts PE.≡ ctr i' j' ts' →
  i PE.≡ i' × j PE.≡ j' × ts PE.≡ ts'
ctr-PE-injectivity {i} {i'} {j} {j'} eq =
  let k≡ , ts≡ = gen-PE-injectivity eq
      i≡ , j≡ = Ctrkind-inj k≡
  in  i≡ , j≡ , map-injective (λ e → proj₂ (GenT-PE-injectivity e)) ts≡
  where
  Ctrkind-inj : Ctrkind i j PE.≡ Ctrkind i' j' → i PE.≡ i' × j PE.≡ j'
  Ctrkind-inj PE.refl = PE.refl , PE.refl

IndRect-PE-injectivity : ∀ {i i' lG lG' P P' t t' ms ms'} →
  IndRect i lG P t ms PE.≡ IndRect i' lG' P' t' ms' →
  i PE.≡ i' × lG PE.≡ lG' × P PE.≡ P' × t PE.≡ t' × ms PE.≡ ms'
IndRect-PE-injectivity {i} {i'} {lG} {lG'} eq =
  let k≡ , ts≡ = gen-PE-injectivity eq
      i≡ , lG≡ = IndRectkind-inj k≡
      P≡ = proj₂ (GenT-PE-injectivity (∷-inj₁ ts≡))
      t≡ = proj₂ (GenT-PE-injectivity (∷-inj₁ (∷-inj₂ ts≡)))
      ms≡ = map-injective (λ e → proj₂ (GenT-PE-injectivity e)) (∷-inj₂ (∷-inj₂ ts≡))
  in  i≡ , lG≡ , P≡ , t≡ , ms≡
  where
  IndRectkind-inj : IndRectkind i lG PE.≡ IndRectkind i' lG' → i PE.≡ i' × lG PE.≡ lG'
  IndRectkind-inj PE.refl = PE.refl , PE.refl

Univ-PE-injectivity : ∀ {r r' l l'} → Univ r l PE.≡ Univ r' l' → r PE.≡ r' × l PE.≡ l'
Univ-PE-injectivity PE.refl = PE.refl , PE.refl

-- Neutral terms.

-- A term is neutral if
-- either it has a variable in head position that blocks reduction.
-- either it is of the form Emptyrec (or terms that should reduce to emptyrec, such as incompatible casts)

-- Representative of an inductive with respect to the equivalences
reprInd : Nat → Nat
reprInd i = Eq.repr equivs i

data Neutral : Term → Set where
  var     : ∀ n                     → Neutral (var n)
  ∘ₙ      : ∀ {k u l}     → Neutral k → Neutral (k ∘ u ^ l)
  castₙ : ∀ {l A B e t} → Neutral A → Neutral B → Neutral t → Neutral (cast l A B e t)
  castnΠₙ : ∀ {l A rA lA P lP r B e t} → Neutral B → Neutral (cast l B (Π A ^ rA ° lA ▹ P ° lP ° l ^ r) e t)
  castΠₙ : ∀ {l A rA lA P lP r B e t} → Neutral B → Neutral (cast l (Π A ^ rA ° lA ▹ P ° lP ° l ^ r) B e t)
  castnIndₙ : ∀ {l i B e t} → Neutral B → Neutral (cast l B (Ind i) e t)
  castIndₙ : ∀ {l i B e t} → Neutral B → Neutral (cast l (Ind i) B e t)
  -- Inductives with different representatives are not related by an
  -- equivalence, so a cast between them is stuck.
  castIndInd≢ₙ : ∀ {l i j e t} → reprInd i PE.≢ reprInd j → Neutral (cast l (Ind i) (Ind j) e t)
  castIndΠₙ : ∀ {l i A rA r B e t} → Neutral (cast l (Ind i) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ r) e t)
  castΠIndₙ : ∀ {l i A rA r B e t} → Neutral (cast l (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ r) (Ind i) e t)
  castΠΠ%!ₙ : ∀ {l A B A' B' r r' e t} → Neutral (cast l (Π A ^ % ° ⁰ ▹ B ° ⁰ ° l ^ r) (Π A' ^ ! ° ⁰ ▹ B' ° ⁰ ° l ^ r') e t)
  castΠΠ!%ₙ : ∀ {l A B A' B' r r' e t} → Neutral (cast l (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° l ^ r) (Π A' ^ % ° ⁰ ▹ B' ° ⁰ ° l ^ r') e t)
  Emptyrecₙ : ∀ {l lEmpty A e} -> Neutral (Emptyrec l lEmpty A e)
  IndRectₙ : ∀ {i lG P t ms} → Neutral t → Neutral (IndRect i lG P t ms)

-- Weak head normal forms (whnfs).
-- These are the (lazy) values of our language.

data Whnf : Term → Set where

  -- Type constructors are whnfs.
  Uₙ    : ∀ {r l} → Whnf (Univ r l)
  Πₙ    : ∀ {A r lA B lB l r'} → Whnf (Π A ^ r ° lA ▹ B ° lB ° l ^ r')
  Idₙ : ∀ {A t u} → Whnf (Id A t u)
  Emptyₙ : ∀ {l} → Whnf (Empty l)
  Indₙ : ∀ {i} → Whnf (Ind i)

  -- Introductions are whnfs.
  lamₙ  : ∀ {A t l} → Whnf (lam A ▹ t ^ l)
  ctrₙ : ∀ {i j ts} → Whnf (ctr i j ts)

  -- Neutrals are whnfs.
  ne   : ∀ {n} → Neutral n → Whnf n

-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢Ind : ∀ {r l i} → Univ r l PE.≢ Ind i
U≢Ind ()

U≢Empty : ∀ {r l l'} → Univ r l PE.≢ Empty l'
U≢Empty ()

U≢Π : ∀ {r r' r'' l F lF G lG l'} → Univ r l PE.≢ Π F ^ r' ° lF ▹ G ° lG ° l' ^ r''
U≢Π ()

U≢Id : ∀ {r l F t u} → Univ r l PE.≢ Id F t u
U≢Id ()

U≢ne : ∀ {r l K} → Neutral K → Univ r l PE.≢ K
U≢ne () PE.refl

Empty≢Ind : ∀ {l i} → Empty l PE.≢ Ind i
Empty≢Ind ()

Ind≢Empty : ∀ {i l} → Ind i PE.≢ Empty l
Ind≢Empty ()

Ind≢Id : ∀ {i F t u} → Ind i PE.≢ Id F t u
Ind≢Id ()

Id≢Ind : ∀ {F t u i} → Id F t u PE.≢ Ind i
Id≢Ind ()

Ind≢Π : ∀ {i F r lF G lG l r'} → Ind i PE.≢ Π F ^ r ° lF ▹ G ° lG ° l ^ r'
Ind≢Π ()

Π≢Ind : ∀ {F r lF G lG l r' i} → Π F ^ r ° lF ▹ G ° lG ° l ^ r' PE.≢ Ind i
Π≢Ind ()

Ind-inj : ∀ {i j} → Ind i PE.≡ Ind j → i PE.≡ j
Ind-inj PE.refl = PE.refl

Empty≢ne : ∀ {l K} → Neutral K → Empty l PE.≢ K
Empty≢ne () PE.refl

Empty≢Π : ∀ {F r lF G lG l l' r'} → Empty l' PE.≢ Π F ^ r ° lF ▹ G ° lG ° l ^ r'
Empty≢Π ()

Empty≢Id : ∀ {l F t u} → Empty l PE.≢ Id F t u
Empty≢Id ()

Π≢ne : ∀ {F r lF G lG K l r'} → Neutral K → Π F ^ r ° lF ▹ G ° lG ° l ^ r' PE.≢ K
Π≢ne () PE.refl

Π≢Id : ∀ {F r lF G lG F' t u l r'} → Π F ^ r ° lF ▹ G ° lG ° l ^ r' PE.≢ Id F' t u
Π≢Id ()

Id≢ne : ∀ {F t u K} → Neutral K → Id F t u PE.≢ K
Id≢ne () PE.refl

ctr≢ne : ∀ {i j args k} → Neutral k → ctr i j args PE.≢ k
ctr≢ne () PE.refl

Ind≢ne : ∀ {i K} → Neutral K → Ind i PE.≢ K
Ind≢ne () PE.refl

Ind≢ctr : ∀ {i j k ts} → Ind i PE.≢ ctr j k ts
Ind≢ctr ()

-- Several views on whnfs (note: not recursive).

-- A whnf of type Ind i is a constructor of Ind i, or neutral.

data Inductive (i : Nat) : Term → Set where
  ctrₙ : ∀ {j ts}           → Inductive i (ctr i j ts)
  ne   : ∀ {n} → Neutral n → Inductive i n

-- A type in whnf is either Π A B, Ind i, or neutral.
-- Large types could also be U.

data Type : Term → Set where
  Πₙ : ∀ {A r lA B lB l r'} → Type (Π A ^ r ° lA ▹ B ° lB ° l ^ r')
  Uₙ : ∀ {r l} → Type (Univ r l)
  Emptyₙ : ∀ {l} → Type (Empty l)
  Idₙ : ∀ {A t u} → Type (Id A t u)
  Indₙ : ∀ {i} → Type (Ind i)
  ne : ∀{n} → Neutral n → Type n

-- A whnf of type Π A B is either lam t or neutral.

data Function : Term → Set where
  lamₙ : ∀{A t l} → Function (lam A ▹ t ^ l)
  ne : ∀{n} → Neutral n → Function n

-- These views classify only whnfs.

-- Inductive, Type, and Function are subsets of Whnf.

inductiveWhnf : ∀ {i t} → Inductive i t → Whnf t
inductiveWhnf ctrₙ = ctrₙ
inductiveWhnf (ne x) = ne x

typeWhnf : ∀ {A} → Type A → Whnf A
typeWhnf Πₙ = Πₙ
typeWhnf Uₙ  = Uₙ
typeWhnf Idₙ = Idₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf Indₙ = Indₙ
typeWhnf (ne x) = ne x

functionWhnf : ∀ {f} → Function f → Whnf f
functionWhnf lamₙ = lamₙ
functionWhnf (ne x) = ne x

------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Set where
  id    : Wk        -- η : Γ ≤ Γ.
  step  : Wk  → Wk  -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : Wk  → Wk  -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  Wk → Wk → Wk
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

repeat : {A : Set} → (A → A) → A → Nat → A
repeat f a 0 = a
repeat f a (1+ n) = f (repeat f a n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar ρ x ∈ dom(Γ).

wkVar : (ρ : Wk) (n : Nat) → Nat
wkVar id       n        = n
wkVar (step ρ) n        = 1+ (wkVar ρ n)
wkVar (lift ρ) 0    = 0
wkVar (lift ρ) (1+ n) = 1+ (wkVar ρ n)

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : (ρ : Wk) (g : List (GenT Term)) → List (GenT Term)
  wkGen ρ [] = []
  wkGen ρ (⟦ l , t ⟧ ∷ g) = ⟦ l , (wk (repeat lift ρ l) t) ⟧ ∷ wkGen ρ g

  wk : (ρ : Wk) (t : Term) → Term
  wk ρ (var x) = var (wkVar ρ x)
  wk ρ (gen x c) = gen x (wkGen ρ c)

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term → Term
wk1 = wk (step id)

wk1d : Term → Term
wk1d = wk (lift (step id))

map-map : ∀ {A B C} (f : B → C) (g : A → B) (xs : List A)
  → map f (map g xs) PE.≡ map (λ x → f (g x)) xs
map-map f g [] = PE.refl
map-map f g (x ∷ xs) = PE.cong (f (g x) ∷_) (map-map f g xs)

map-cong : ∀ {A B} {f g : A → B} (xs : List A)
  → (∀ x → f x PE.≡ g x) → map f xs PE.≡ map g xs
map-cong [] eq = PE.refl
map-cong (x ∷ xs) eq = PE.cong₂ _∷_ (eq x) (map-cong xs eq)

wkGen-map0 : ∀ ρ ts → wkGen ρ (map (λ t → ⟦ 0 , t ⟧) ts) PE.≡ map (λ t → ⟦ 0 , wk ρ t ⟧) ts
wkGen-map0 ρ [] = PE.refl
wkGen-map0 ρ (t ∷ ts) = PE.cong (⟦ 0 , wk ρ t ⟧ ∷_) (wkGen-map0 ρ ts)

map-map0-wkGen : ∀ ρ ts
  → map (λ t → ⟦ 0 , t ⟧) (map (wk ρ) ts) PE.≡ wkGen ρ (map (λ t → ⟦ 0 , t ⟧) ts)
map-map0-wkGen ρ ts = PE.trans (map-map (λ t → ⟦ 0 , t ⟧) (wk ρ) ts) (PE.sym (wkGen-map0 ρ ts))

wk-IndRect : ∀ ρ i lG P t ms →
  wk ρ (IndRect i lG P t ms) PE.≡
  IndRect i lG (wk (lift ρ) P) (wk ρ t) (map (wk ρ) ms)
wk-IndRect ρ i lG P t ms =
  PE.cong (λ gs → gen (IndRectkind i lG) (⟦ 1 , wk (lift ρ) P ⟧ ∷ ⟦ 0 , wk ρ t ⟧ ∷ gs))
    (PE.sym (map-map0-wkGen ρ ms))

wk-ctr : ∀ ρ i j ts →
  wk ρ (ctr i j ts) PE.≡ ctr i j (map (wk ρ) ts)
wk-ctr ρ i j ts =
  PE.cong (gen (Ctrkind i j)) (PE.sym (map-map0-wkGen ρ ts))

-- Weakening of a neutral term.

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n)    = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)    = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (IndRectₙ {i} {lG} {P} {t} {ms} n) =
  PE.subst Neutral (PE.sym (wk-IndRect ρ i lG P t ms))
    (IndRectₙ {P = wk (lift ρ) P} {ms = map (wk ρ) ms} (wkNeutral ρ n))
wkNeutral ρ Emptyrecₙ = Emptyrecₙ
wkNeutral ρ (castₙ A B t) = castₙ (wkNeutral ρ A) (wkNeutral ρ B) (wkNeutral ρ t)
wkNeutral ρ (castnΠₙ A) = castnΠₙ (wkNeutral ρ A)
wkNeutral ρ (castΠₙ A) = castΠₙ (wkNeutral ρ A)
wkNeutral ρ (castnIndₙ A) = castnIndₙ (wkNeutral ρ A)
wkNeutral ρ (castIndₙ A) = castIndₙ (wkNeutral ρ A)
wkNeutral ρ (castIndInd≢ₙ p) = castIndInd≢ₙ p
wkNeutral ρ castIndΠₙ = castIndΠₙ
wkNeutral ρ castΠIndₙ = castΠIndₙ
wkNeutral ρ castΠΠ%!ₙ = castΠΠ%!ₙ
wkNeutral ρ castΠΠ!%ₙ = castΠΠ!%ₙ

-- Weakening can be applied to our whnf views.

wkInductive : ∀ {i t} ρ → Inductive i t → Inductive i (wk ρ t)
wkInductive ρ (ctrₙ {j} {ts}) =
  PE.subst (Inductive _) (PE.cong (gen (Ctrkind _ j)) (map-map0-wkGen ρ ts))
    (ctrₙ {ts = map (wk ρ) ts})
wkInductive ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ {t} ρ → Type t → Type (wk ρ t)
wkType ρ Πₙ      = Πₙ
wkType ρ Uₙ      = Uₙ
wkType ρ Idₙ      = Idₙ
wkType ρ Emptyₙ  = Emptyₙ
wkType ρ Indₙ    = Indₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ {t} ρ → Function t → Function (wk ρ t)
wkFunction ρ lamₙ    = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ {t} ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ Idₙ      = Idₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)
wkWhnf ρ (ctrₙ {i} {j} {ts}) = PE.subst Whnf (PE.cong (gen (Ctrkind i j)) (map-map0-wkGen ρ ts)) (ctrₙ {ts = map (wk ρ) ts})
wkWhnf ρ Indₙ = Indₙ

-- Non-dependent version of Π.

_^_°_▹▹_°_°_^_ : Term → Relevance → Level → Term → Level → Level → Relevance → Term
A ^ r ° lA ▹▹ B ° lB ° l ^ r' = Π A ^ r ° lA ▹ wk1 B ° lB ° l ^ r'

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : Set
Subst = Nat → Term

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ subst σ t : subst σ A.
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst → Term
head σ = σ 0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst → Subst
tail σ n = σ (1+ n)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst) (x : Nat) → Term
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst → Subst
wk1Subst σ x = wk1 (σ x)

-- Weaken a substitution by [d].
--
-- If Γ ⊢ σ : Δ then Γ∙A₁∙…∙A_d ⊢ wk1^Subst d σ : Δ.

wk1^Subst : Nat → Subst → Subst
wk1^Subst 0 σ = σ
wk1^Subst (1+ d) σ = wk1Subst (wk1^Subst d σ)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst) → Subst
liftSubst σ 0    = var 0
liftSubst σ (1+ x) = wk1Subst σ x

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst : Wk → Subst
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : (σ : Subst) (g : List (GenT Term)) → List (GenT Term)
  substGen σ [] = []
  substGen σ (⟦ l , t ⟧ ∷ g) = ⟦ l , (subst (repeat liftSubst σ l) t) ⟧ ∷ substGen σ g

  subst : (σ : Subst) (t : Term) → Term
  subst σ (var x) = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst → Term → Subst
consSubst σ t 0    = t
consSubst σ t (1+ n) = σ n

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term → Subst
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst → Subst → Subst
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk → Subst → Subst
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst → Wk → Subst
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term) (s : Term) → Term
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t

_[_]↑↑ : (t : Term) (s : Term) → Term
t [ s ]↑↑ = subst (consSubst (wk1Subst (wk1Subst idSubst)) s) t

-- Substitute the first variable of a term with an other term living
-- under [d] extra binders.
--
-- If Γ∙A ⊢ t : B and Γ∙B₁∙…∙B_d ⊢ s : A then Γ∙B₁∙…∙B_d ⊢ t[s]↑^ d : B[s]↑^ d.

_[_]↑^_ : (t : Term) (s : Term) (d : Nat) → Term
t [ s ]↑^ d = subst (consSubst (wk1^Subst d idSubst) s) t

------------------------------------------------------------------------
-- IndRect helpers

wk1^ : Nat → Term → Term
wk1^ 0 t = t
wk1^ (1+ n) t = wk1 (wk1^ n t)

-- Left-nested applications [t ∘ u0 ∘ … ∘ uk] at level l.
apps : Level → Term → List Term → Term
apps l t us = foldl (λ f u → f ∘ u ^ l) t us

apps-∷≢Univ : ∀ l t u us {r} → apps l t (u ∷ us) PE.≢ Univ r ¹
apps-∷≢Univ l t u [] ()
apps-∷≢Univ l t u (u′ ∷ us) eq = apps-∷≢Univ l (t ∘ u ^ l) u′ us eq

-- Recursive constructor arguments only (left-to-right).
ctrRecArgs : Nat → List SU.Type → List Term → List Term
ctrRecArgs ind Ss args =
  map proj₁
    (filter (λ aT → SU.ctrArgIsRecursive ind (proj₂ aT))
      (zip args Ss))

map-ctrRecArgs : ∀ (f : Term → Term) ind Ss args →
  map f (ctrRecArgs ind Ss args) PE.≡ ctrRecArgs ind Ss (map f args)
map-ctrRecArgs f ind Ss [] = PE.refl
map-ctrRecArgs f ind [] (a ∷ args) = PE.refl
map-ctrRecArgs f ind (S ∷ Ss) (a ∷ args) with SU.ctrArgIsRecursive ind S
... | true  = PE.cong (f a ∷_) (map-ctrRecArgs f ind Ss args)
... | false = map-ctrRecArgs f ind Ss args

-- wk of IndRect β redex RHS
wk-IndRect-ctr-rhs : ∀ ρ i Ts lG P m args ms →
  let rhs = apps lG m (args ++ map (λ a → IndRect i lG P a ms) (ctrRecArgs i Ts args))
  in wk ρ rhs PE.≡
     apps lG (wk ρ m)
              (map (wk ρ) args ++
                map (λ a → IndRect i lG (wk (lift ρ) P) a (map (wk ρ) ms))
                    (ctrRecArgs i Ts (map (wk ρ) args)))
wk-IndRect-ctr-rhs ρ i Ts lG P m args ms =
  PE.trans (wk-apps ρ lG m
              (args ++ map (λ a → IndRect i lG P a ms) recs))
       (PE.cong₂ (apps lG)
         PE.refl
         (PE.trans (map-++ (wk ρ) args (map (λ a → IndRect i lG P a ms) recs))
           (PE.cong₂ _++_ PE.refl
             (PE.trans (map-map (wk ρ) (λ a → IndRect i lG P a ms) recs)
               (PE.trans (map-cong recs (λ a → wk-IndRect ρ i lG P a ms))
                 (PE.trans (PE.sym (map-map (λ a → IndRect i lG (wk (lift ρ) P) a (map (wk ρ) ms))
                                            (wk ρ) recs))
                           (PE.cong (map (λ a → IndRect i lG (wk (lift ρ) P) a (map (wk ρ) ms)))
                                    (map-ctrRecArgs (wk ρ) i Ts args))))))))
  where
    recs = ctrRecArgs i Ts args

    wk-apps : ∀ ρ l t us →
      wk ρ (apps l t us) PE.≡ apps l (wk ρ t) (map (wk ρ) us)
    wk-apps ρ l t [] = PE.refl
    wk-apps ρ l t (u ∷ us) = wk-apps ρ l (t ∘ u ^ l) us

substGen-map0 : ∀ σ ts →
  substGen σ (map (λ t → ⟦ 0 , t ⟧) ts) PE.≡ map (λ t → ⟦ 0 , subst σ t ⟧) ts
substGen-map0 σ [] = PE.refl
substGen-map0 σ (t ∷ ts) = PE.cong (⟦ 0 , subst σ t ⟧ ∷_) (substGen-map0 σ ts)

subst-IndRect : ∀ σ i lG P t ms →
  subst σ (IndRect i lG P t ms) PE.≡
  IndRect i lG (subst (liftSubst σ) P) (subst σ t) (map (subst σ) ms)
subst-IndRect σ i lG P t ms =
  PE.cong (λ gs → gen (IndRectkind i lG) (⟦ 1 , subst (liftSubst σ) P ⟧ ∷ ⟦ 0 , subst σ t ⟧ ∷ gs))
    (PE.trans (substGen-map0 σ ms)
              (PE.sym (map-map (λ m → ⟦ 0 , m ⟧) (subst σ) ms)))

subst-ctr : ∀ σ i j ts →
  subst σ (ctr i j ts) PE.≡ ctr i j (map (subst σ) ts)
subst-ctr σ i j ts =
  PE.cong (gen (Ctrkind i j))
    (PE.trans (substGen-map0 σ ts)
              (PE.sym (map-map (λ t → ⟦ 0 , t ⟧) (subst σ) ts)))

subst-IndRect-ctr-rhs : ∀ σ i Ts lG P m args ms →
  let rhs = apps lG m (args ++ map (λ a → IndRect i lG P a ms) (ctrRecArgs i Ts args))
  in subst σ rhs PE.≡
     apps lG (subst σ m)
              (map (subst σ) args ++
                map (λ a → IndRect i lG (subst (liftSubst σ) P) a (map (subst σ) ms))
                    (ctrRecArgs i Ts (map (subst σ) args)))
subst-IndRect-ctr-rhs σ i Ts lG P m args ms =
  PE.trans (subst-apps σ lG m
              (args ++ map (λ a → IndRect i lG P a ms) recs))
       (PE.cong₂ (apps lG)
         PE.refl
         (PE.trans (map-++ (subst σ) args (map (λ a → IndRect i lG P a ms) recs))
           (PE.cong₂ _++_ PE.refl
             (PE.trans (map-map (subst σ) (λ a → IndRect i lG P a ms) recs)
               (PE.trans (map-cong recs (λ a → subst-IndRect σ i lG P a ms))
                 (PE.trans (PE.sym (map-map (λ a → IndRect i lG (subst (liftSubst σ) P) a (map (subst σ) ms))
                                            (subst σ) recs))
                           (PE.cong (map (λ a → IndRect i lG (subst (liftSubst σ) P) a (map (subst σ) ms)))
                                    (map-ctrRecArgs (subst σ) i Ts args))))))))
  where
    recs = ctrRecArgs i Ts args

    subst-apps : ∀ σ l t us →
      subst σ (apps l t us) PE.≡ apps l (subst σ t) (map (subst σ) us)
    subst-apps σ l t [] = PE.refl
    subst-apps σ l t (u ∷ us) = subst-apps σ l (t ∘ u ^ l) us

-- Constructor argument types as (type, level), embedding of simple signatures.
ctrArgsTypeList : List SU.Type → List (Term × Nat)
ctrArgsTypeList Ss =
  map (λ p → (emb-oterm (proj₁ p) , proj₂ p)) (O.ctrArgsTypeList Ss)

-- Indices of recursive arguments in a constructor (left-to-right).
ctrRecIndices : Nat → List SU.Type → List Nat
ctrRecIndices ind Ss =
  map proj₁
    (filter (λ jT → SU.ctrArgIsRecursive ind (proj₂ jT))
      (zip (range (length Ss)) Ss))

-- CIC method type for the constructor [index] of [ind] with argument types
-- [Ss] at motive [P]:
--   Π (x_i : A_i). Π (ih_j : P x_j)_{A_j = I}. P (c x⃗)
-- The motive is a type family over [ind], instantiated with [_[_]↑^_].
indRectBranchTy : Nat → Nat → List SU.Type → Term → Relevance → Level → Term
indRectBranchTy ind index Ss P rG lG =
  let Ts = ctrArgsTypeList Ss
      n = length Ts
      recs = ctrRecIndices ind Ss
      k = length recs
      vars = map (λ j → var (((k + n) - 1) - j)) (range n)
      conclusion = P [ ctr ind index vars ]↑^ (k + n)
      ihTys = map (λ pj →
                P [ var (((n - 1) - proj₁ pj) + proj₂ pj) ]↑^ (n + proj₂ pj))
                (zip recs (range k))
      argTys = map proj₁ Ts
  in  foldr (λ A B → Π A ^ ! ° ⁰ ▹ B ° lG ° lG ^ rG)
        (foldr (λ A B → Π A ^ rG ° lG ▹ B ° lG ° lG ^ rG) conclusion ihTys)
        argTys

indRectBranchTyList : SU.SInd → Term → Relevance → Level → List Term
indRectBranchTyList ind P rG lG =
  map (λ jTs → indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P rG lG)
      (zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind))

------------------------------------------------------------------------
-- Embedding homomorphism lemmas

emb-substσ : O.Subst → Subst
emb-substσ σ x = emb-oterm (σ x)

emb-Wk : O.Wk → Wk
emb-Wk O.id = id
emb-Wk (O.step ρ) = step (emb-Wk ρ)
emb-Wk (O.lift ρ) = lift (emb-Wk ρ)

emb-Wk-repeat-lift : ∀ ρ l → emb-Wk (O.repeat O.lift ρ l) PE.≡ repeat lift (emb-Wk ρ) l
emb-Wk-repeat-lift ρ 0 = PE.refl
emb-Wk-repeat-lift ρ (1+ l) = PE.cong lift (emb-Wk-repeat-lift ρ l)

emb-wkVar : ∀ ρ x → O.wkVar ρ x PE.≡ wkVar (emb-Wk ρ) x
emb-wkVar O.id x = PE.refl
emb-wkVar (O.step ρ) x = PE.cong 1+ (emb-wkVar ρ x)
emb-wkVar (O.lift ρ) 0 = PE.refl
emb-wkVar (O.lift ρ) (1+ x) = PE.cong 1+ (emb-wkVar ρ x)

mutual
  emb-wkGen : ∀ ρ gs → emb-otermGen (O.wkGen ρ gs) PE.≡ wkGen (emb-Wk ρ) (emb-otermGen gs)
  emb-wkGen ρ [] = PE.refl
  emb-wkGen ρ (⟦ l , t ⟧ ∷ gs) =
    PE.cong₂ _∷_
      (PE.cong (⟦_,_⟧ l)
        (PE.trans (emb-wk (O.repeat O.lift ρ l) t)
          (PE.cong (λ ρ' → wk ρ' (emb-oterm t)) (emb-Wk-repeat-lift ρ l))))
      (emb-wkGen ρ gs)

  emb-wk : ∀ ρ t → emb-oterm (O.wk ρ t) PE.≡ wk (emb-Wk ρ) (emb-oterm t)
  emb-wk ρ (O.var x) = PE.cong var (emb-wkVar ρ x)
  emb-wk ρ (O.gen k gs) = PE.cong (gen (emb-okind k)) (emb-wkGen ρ gs)

emb-wk1 : ∀ t → emb-oterm (O.wk1 t) PE.≡ wk1 (emb-oterm t)
emb-wk1 t = emb-wk (O.step O.id) t

emb-substσ-repeat-liftSubst : ∀ σ l x →
  emb-substσ (O.repeat O.liftSubst σ l) x PE.≡ repeat liftSubst (emb-substσ σ) l x
emb-substσ-repeat-liftSubst σ 0 x = PE.refl
emb-substσ-repeat-liftSubst σ (1+ l) 0 = PE.refl
emb-substσ-repeat-liftSubst σ (1+ l) (1+ x) =
  PE.trans (emb-wk1 (O.repeat O.liftSubst σ l x))
    (PE.cong wk1 (emb-substσ-repeat-liftSubst σ l x))

emb-substσ-repeat-liftSubst-eq : ∀ (σ : O.Subst) (σ' : Subst) l x →
  (∀ x → emb-substσ σ x PE.≡ σ' x) →
  repeat liftSubst (emb-substσ σ) l x PE.≡ repeat liftSubst σ' l x
emb-substσ-repeat-liftSubst-eq σ σ' 0 x eq = eq x
emb-substσ-repeat-liftSubst-eq σ σ' (1+ l) 0 eq = PE.refl
emb-substσ-repeat-liftSubst-eq σ σ' (1+ l) (1+ x) eq =
  PE.cong wk1 (emb-substσ-repeat-liftSubst-eq σ σ' l x eq)

mutual
  emb-substGen-eq : ∀ {σ σ'} → (∀ x → emb-substσ σ x PE.≡ σ' x) → ∀ gs →
    emb-otermGen (O.substGen σ gs) PE.≡ substGen σ' (emb-otermGen gs)
  emb-substGen-eq eq [] = PE.refl
  emb-substGen-eq {σ} {σ'} eq (⟦ l , t ⟧ ∷ gs) =
    PE.cong₂ _∷_
      (PE.cong (⟦_,_⟧ l)
        (emb-substσ-eq {σ = O.repeat O.liftSubst σ l}
                       {σ' = repeat liftSubst σ' l}
                       (λ x → PE.trans (emb-substσ-repeat-liftSubst σ l x)
                                       (emb-substσ-repeat-liftSubst-eq σ σ' l x eq)) t))
      (emb-substGen-eq eq gs)

  emb-substσ-eq : ∀ {σ : O.Subst} {σ' : Subst} →
    (∀ x → emb-substσ σ x PE.≡ σ' x) → ∀ (t : OTerm) →
    emb-oterm (O.subst σ t) PE.≡ subst σ' (emb-oterm t)
  emb-substσ-eq eq (O.var x) = eq x
  emb-substσ-eq {σ} {σ'} eq (O.gen k gs) =
    PE.cong (gen (emb-okind k)) (emb-substGen-eq eq gs)

  emb-substGen : ∀ σ gs → emb-otermGen (O.substGen σ gs) PE.≡ substGen (emb-substσ σ) (emb-otermGen gs)
  emb-substGen σ [] = PE.refl
  emb-substGen σ (⟦ l , t ⟧ ∷ gs) =
    PE.cong₂ _∷_
      (PE.cong (⟦_,_⟧ l)
        (emb-substσ-eq {σ = O.repeat O.liftSubst σ l}
                       {σ' = repeat liftSubst (emb-substσ σ) l}
                       (emb-substσ-repeat-liftSubst σ l) t))
      (emb-substGen σ gs)

  emb-subst : ∀ (σ : O.Subst) (t : OTerm) →
    emb-oterm (O.subst σ t) PE.≡ subst (emb-substσ σ) (emb-oterm t)
  emb-subst σ (O.var x) = PE.refl
  emb-subst σ (O.gen k gs) = PE.cong (gen (emb-okind k)) (emb-substGen σ gs)

emb-substσ-wk1Subst : ∀ σ x → emb-substσ (O.wk1Subst σ) x PE.≡ wk1 (emb-substσ σ x)
emb-substσ-wk1Subst σ x = emb-wk1 (σ x)

emb-substσ-consSubst : ∀ σ t x → emb-substσ (O.consSubst σ t) x PE.≡ consSubst (emb-substσ σ) (emb-oterm t) x
emb-substσ-consSubst σ t 0 = PE.refl
emb-substσ-consSubst σ t (1+ x) = PE.refl

emb-substσ-consSubst-wk1 : ∀ s n →
  emb-substσ (O.consSubst (O.wk1Subst O.idSubst) s) n
  PE.≡ consSubst (wk1Subst idSubst) (emb-oterm s) n
emb-substσ-consSubst-wk1 s 0 = PE.refl
emb-substσ-consSubst-wk1 s (1+ n) = emb-substσ-wk1Subst O.idSubst n

emb-sgSubst : ∀ t s → emb-oterm (t O.[ s ]) PE.≡ emb-oterm t [ emb-oterm s ]
emb-sgSubst t s = emb-substσ-eq (emb-substσ-consSubst O.idSubst s) t

emb-liftSubst : ∀ t s → emb-oterm (t O.[ s ]↑) PE.≡ emb-oterm t [ emb-oterm s ]↑
emb-liftSubst t s = emb-substσ-eq (λ n → emb-substσ-consSubst-wk1 s n) t

emb-substσ-wk1^Subst : ∀ d σ x →
  emb-substσ (O.wk1^Subst d σ) x PE.≡ wk1^Subst d (emb-substσ σ) x
emb-substσ-wk1^Subst 0 σ x = PE.refl
emb-substσ-wk1^Subst (1+ d) σ x =
  PE.trans (emb-substσ-wk1Subst (O.wk1^Subst d σ) x)
    (PE.cong wk1 (emb-substσ-wk1^Subst d σ x))

emb-substσ-consSubst-wk1^ : ∀ d s n →
  emb-substσ (O.consSubst (O.wk1^Subst d O.idSubst) s) n
  PE.≡ consSubst (wk1^Subst d idSubst) (emb-oterm s) n
emb-substσ-consSubst-wk1^ d s 0 = PE.refl
emb-substσ-consSubst-wk1^ d s (1+ n) = emb-substσ-wk1^Subst d O.idSubst n

emb-liftSubst^ : ∀ t s d →
  emb-oterm (t O.[ s ]↑^ d) PE.≡ emb-oterm t [ emb-oterm s ]↑^ d
emb-liftSubst^ t s d = emb-substσ-eq (λ n → emb-substσ-consSubst-wk1^ d s n) t

emb-Π : ∀ A r lA B lB l r' →
  emb-oterm (O.Π A ^ r ° lA ▹ B ° lB ° l ^ r') PE.≡
  Π (emb-oterm A) ^ r ° lA ▹ (emb-oterm B) ° lB ° l ^ r'
emb-Π A r lA B lB l r' = PE.refl

emb-▹▹ : ∀ A r lA B lB l r' →
  emb-oterm (O.Π A ^ r ° lA ▹ O.wk1 B ° lB ° l ^ r') PE.≡
  emb-oterm A ^ r ° lA ▹▹ emb-oterm B ° lB ° l ^ r'
emb-▹▹ A r lA B lB l r' =
  PE.trans (emb-Π A r lA (O.wk1 B) lB l r')
    (PE.cong (λ T → Π (emb-oterm A) ^ r ° lA ▹ T ° lB ° l ^ r') (emb-wk1 B))

emb-wk1-liftSubst : ∀ G s →
  wk1 (emb-oterm (G O.[ s ]↑)) PE.≡ wk1 (emb-oterm G [ emb-oterm s ]↑)
emb-wk1-liftSubst G s = PE.cong wk1 (emb-liftSubst G s)

emb-lam : ∀ A t l →
  emb-oterm (O.lam A ▹ t ^ l) PE.≡ lam (emb-oterm A) ▹ emb-oterm t ^ l
emb-lam A t l = PE.refl

emb-∘ : ∀ t u l →
  emb-oterm (t O.∘ u ^ l) PE.≡ emb-oterm t ∘ emb-oterm u ^ l
emb-∘ t u l = PE.refl

emb-wk1∘var : ∀ f l →
  emb-oterm (O.wk1 f O.∘ O.var Nat.zero ^ l) PE.≡
  wk1 (emb-oterm f) ∘ var Nat.zero ^ l
emb-wk1∘var f l =
  PE.trans (emb-∘ (O.wk1 f) (O.var Nat.zero) l)
    (PE.cong (λ t → t ∘ var Nat.zero ^ l) (emb-wk1 f))

emb-cast : ∀ l A B e t →
  emb-oterm (O.cast l A B e t) PE.≡
  cast l (emb-oterm A) (emb-oterm B) (emb-oterm e) (emb-oterm t)
emb-cast l A B e t = PE.refl

emb-Id : ∀ A t u →
  emb-oterm (O.Id A t u) PE.≡ Id (emb-oterm A) (emb-oterm t) (emb-oterm u)
emb-Id A t u = PE.refl

emb-Idrefl : ∀ A t →
  emb-oterm (O.Idrefl A t) PE.≡ Idrefl (emb-oterm A) (emb-oterm t)
emb-Idrefl A t = PE.refl

emb-transp : ∀ A P t s u e →
  emb-oterm (O.transp A P t s u e) PE.≡
  transp (emb-oterm A) (emb-oterm P) (emb-oterm t)
         (emb-oterm s) (emb-oterm u) (emb-oterm e)
emb-transp A P t s u e = PE.refl

emb-fst : ∀ e → emb-oterm (O.fst e) PE.≡ fst (emb-oterm e)
emb-fst e = PE.refl

emb-snd : ∀ e → emb-oterm (O.snd e) PE.≡ snd (emb-oterm e)
emb-snd e = PE.refl

emb-Emptyrec : ∀ lA A e →
  emb-oterm (O.Emptyrec lA ⁰ A e) PE.≡ Emptyrec lA ⁰ (emb-oterm A) (emb-oterm e)
emb-Emptyrec lA A e = PE.refl

emb-Ind : ∀ i → emb-oterm (O.Ind i) PE.≡ Ind i
emb-Ind i = PE.refl

emb-otermGen-map0 : ∀ ts →
  emb-otermGen (map (λ t → ⟦ 0 , t ⟧) ts) PE.≡ map (λ t → ⟦ 0 , emb-oterm t ⟧) ts
emb-otermGen-map0 [] = PE.refl
emb-otermGen-map0 (t ∷ ts) = PE.cong (⟦ 0 , emb-oterm t ⟧ ∷_) (emb-otermGen-map0 ts)

emb-oterm-all : List OTerm → List Term
emb-oterm-all [] = []
emb-oterm-all (t ∷ ts) = emb-oterm t ∷ emb-oterm-all ts

emb-oterm-all-map : ∀ ts → emb-oterm-all ts PE.≡ map emb-oterm ts
emb-oterm-all-map [] = PE.refl
emb-oterm-all-map (t ∷ ts) = PE.cong (emb-oterm t ∷_) (emb-oterm-all-map ts)

emb-stype : SU.Type → Term
emb-stype (SU.Ind i) = Ind i
emb-stype (SU.Arrow A B) = Π (emb-stype A) ^ ! ° ⁰ ▹ emb-stype B ° ⁰ ° ⁰ ^ !

emb-stype-hom : ∀ T → emb-oterm (O.emb-stype-oterm T) PE.≡ emb-stype T
emb-stype-hom (SU.Ind i) = PE.refl
emb-stype-hom (SU.Arrow A B) =
  PE.cong₂ (λ A′ B′ → Π A′ ^ ! ° ⁰ ▹ B′ ° ⁰ ° ⁰ ^ !)
    (emb-stype-hom A) (emb-stype-hom B)

wk-emb-stype : ∀ ρ A → wk ρ (emb-stype A) PE.≡ emb-stype A
wk-emb-stype ρ (SU.Ind i) = PE.refl
wk-emb-stype ρ (SU.Arrow A B) =
  PE.cong₂ (λ A′ B′ → Π A′ ^ ! ° ⁰ ▹ B′ ° ⁰ ° ⁰ ^ !)
    (wk-emb-stype ρ A) (wk-emb-stype (lift ρ) B)

map-wk-emb-stype : ∀ ρ As →
  map (wk ρ) (map emb-stype As) PE.≡ map emb-stype As
map-wk-emb-stype ρ [] = PE.refl
map-wk-emb-stype ρ (A ∷ As) =
  PE.cong₂ _∷_ (wk-emb-stype ρ A) (map-wk-emb-stype ρ As)

subst-emb-stype : ∀ σ A → subst σ (emb-stype A) PE.≡ emb-stype A
subst-emb-stype σ (SU.Ind i) = PE.refl
subst-emb-stype σ (SU.Arrow A B) =
  PE.cong₂ (λ A′ B′ → Π A′ ^ ! ° ⁰ ▹ B′ ° ⁰ ° ⁰ ^ !)
    (subst-emb-stype σ A) (subst-emb-stype (liftSubst σ) B)

map-subst-emb-stype : ∀ σ As →
  map (subst σ) (map emb-stype As) PE.≡ map emb-stype As
map-subst-emb-stype σ [] = PE.refl
map-subst-emb-stype σ (A ∷ As) =
  PE.cong₂ _∷_ (subst-emb-stype σ A) (map-subst-emb-stype σ As)

emb-ctr : ∀ i j ts →
  emb-oterm (O.ctr i j ts) PE.≡ ctr i j (map emb-oterm ts)
emb-ctr i j ts =
  PE.cong (gen (Ctrkind i j))
    (PE.trans (emb-otermGen-map0 ts)
              (PE.sym (map-map (λ t → ⟦ 0 , t ⟧) emb-oterm ts)))

emb-map-Ind : ∀ ns → map emb-oterm (map O.Ind ns) PE.≡ map Ind ns
emb-map-Ind [] = PE.refl
emb-map-Ind (n ∷ ns) = PE.cong (Ind n ∷_) (emb-map-Ind ns)

emb-IndRect : ∀ i lG P t ms →
  emb-oterm (O.IndRect i lG P t ms) PE.≡
  IndRect i lG (emb-oterm P) (emb-oterm t) (emb-oterm-all ms)
emb-IndRect i lG P t ms =
  PE.cong (λ gs → gen (IndRectkind i lG) (⟦ 1 , emb-oterm P ⟧ ∷ ⟦ 0 , emb-oterm t ⟧ ∷ gs))
    (PE.trans (emb-otermGen-map0 ms)
              (PE.trans (PE.sym (map-map (λ m → ⟦ 0 , m ⟧) emb-oterm ms))
                        (PE.cong (map (λ m → ⟦ 0 , m ⟧)) (PE.sym (emb-oterm-all-map ms)))))

emb-indRectBranchTy : ∀ ind index Ss P rG lG →
  emb-oterm (O.indRectBranchTy ind index Ss P rG lG) PE.≡
  indRectBranchTy ind index Ss (emb-oterm P) rG lG
emb-indRectBranchTy ind index Ss P rG lG =
  PE.trans
    (emb-foldr-Π ! ⁰ lG rG (map proj₁ (O.ctrArgsTypeList Ss))
      (foldr (λ A B → O.Π A ^ rG ° lG ▹ B ° lG ° lG ^ rG) concO ihTysO))
    (PE.trans
      (PE.cong₂ (foldr (λ A B → Π A ^ ! ° ⁰ ▹ B ° lG ° lG ^ rG))
        (PE.trans (emb-foldr-Π rG lG lG rG ihTysO concO)
          (PE.cong₂ (foldr (λ A B → Π A ^ rG ° lG ▹ B ° lG ° lG ^ rG))
            (PE.trans (emb-liftSubst^ P
                          (O.ctr ind index (map (λ j → O.var (((k + n) - 1) - j)) (range n)))
                          (k + n))
              (PE.cong (λ t → emb-oterm P [ t ]↑^ (k + n))
                (PE.trans (emb-ctr ind index (map (λ j → O.var (((k + n) - 1) - j)) (range n)))
                  (PE.cong (ctr ind index)
                    (PE.trans
                      (PE.cong (map emb-oterm)
                        (PE.sym (map-map O.var (λ j → ((k + n) - 1) - j) (range n))))
                      (PE.trans (emb-map-var (map (λ j → ((k + n) - 1) - j) (range n)))
                        (map-map var (λ j → ((k + n) - 1) - j) (range n))))))))
            (PE.trans (map-map emb-oterm
                          (λ pj → P O.[ O.var (((n - 1) - proj₁ pj) + proj₂ pj) ]↑^ (n + proj₂ pj))
                          (zip recs (range (length recs))))
              (map-cong (zip recs (range (length recs)))
                (λ pj → emb-liftSubst^ P (O.var (((n - 1) - proj₁ pj) + proj₂ pj))
                                         (n + proj₂ pj))))))
        (PE.trans (map-map emb-oterm proj₁ (O.ctrArgsTypeList Ss))
          (PE.trans (PE.sym (map-map proj₁ (λ p → (emb-oterm (proj₁ p) , proj₂ p))
                               (O.ctrArgsTypeList Ss)))
            PE.refl)))
      (PE.cong₂ (λ n′ recs′ →
          foldr (λ A B → Π A ^ ! ° ⁰ ▹ B ° lG ° lG ^ rG)
            (foldr (λ A B → Π A ^ rG ° lG ▹ B ° lG ° lG ^ rG)
              (emb-oterm P
                [ ctr ind index (map (λ j → var (((length recs′ + n′) - 1) - j))
                                    (range n′)) ]↑^ (length recs′ + n′))
              (map (λ pj → emb-oterm P
                              [ var (((n′ - 1) - proj₁ pj) + proj₂ pj) ]↑^ (n′ + proj₂ pj))
                   (zip recs′ (range (length recs′)))))
            (map proj₁ (ctrArgsTypeList Ss)))
        (PE.sym (length-map (λ p → (emb-oterm (proj₁ p) , proj₂ p))
                   (O.ctrArgsTypeList Ss)))
        emb-ctrRecIndices))
  where
  n = length (O.ctrArgsTypeList Ss)
  recs = O.ctrRecIndices ind Ss
  k = length recs
  ihTysO = map (λ pj → P O.[ O.var (((n - 1) - proj₁ pj) + proj₂ pj) ]↑^ (n + proj₂ pj))
               (zip recs (range k))
  concO = P O.[ O.ctr ind index (map (λ j → O.var (((k + n) - 1) - j)) (range n)) ]↑^ (k + n)

  emb-foldr-Π : ∀ rA lA l r As B →
    emb-oterm (foldr (λ A B → O.Π A ^ rA ° lA ▹ B ° l ° l ^ r) B As) PE.≡
    foldr (λ A B → Π A ^ rA ° lA ▹ B ° l ° l ^ r) (emb-oterm B) (map emb-oterm As)
  emb-foldr-Π rA lA l r [] B = PE.refl
  emb-foldr-Π rA lA l r (A ∷ As) B =
    PE.cong (λ B′ → Π emb-oterm A ^ rA ° lA ▹ B′ ° l ° l ^ r)
      (emb-foldr-Π rA lA l r As B)

  emb-map-var : ∀ ns → map emb-oterm (map O.var ns) PE.≡ map var ns
  emb-map-var [] = PE.refl
  emb-map-var (n ∷ ns) = PE.cong (var n ∷_) (emb-map-var ns)

  emb-ctrRecIndices : O.ctrRecIndices ind Ss PE.≡ ctrRecIndices ind Ss
  emb-ctrRecIndices = PE.refl

emb-indRectBranchTyList : ∀ ind P rG lG →
  map emb-oterm (O.indRectBranchTyList ind P rG lG)
  PE.≡ indRectBranchTyList ind (emb-oterm P) rG lG
emb-indRectBranchTyList ind P rG lG =
  PE.trans (map-map emb-oterm
              (λ jTs → O.indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P rG lG)
              ctrs)
    (map-cong ctrs
      (λ jTs → emb-indRectBranchTy (SU.SInd.name ind) (proj₁ jTs) (proj₂ jTs) P rG lG))
  where
  ctrs = zip (range (SU.indCtrCount ind)) (SU.SInd.ctrArgsTypes ind)

-- Definition of syntaxic sugar

sUnit : Term
sUnit =  Π sEmpty ^ % ° ⁰ ▹ sEmpty ° ⁰ ° ⁰ ^ %

Idsym : (A x y e : Term) → Term
Idsym A x y e = transp A (Id (wk1 A) (var 0) (wk1 x)) x (Idrefl A x) y e

emb-Idsym : ∀ A x y e →
  emb-oterm (O.Idsym A x y e) PE.≡
  Idsym (emb-oterm A) (emb-oterm x) (emb-oterm y) (emb-oterm e)
emb-Idsym A x y e =
  PE.cong (λ P → transp (emb-oterm A) P (emb-oterm x)
             (Idrefl (emb-oterm A) (emb-oterm x))
             (emb-oterm y) (emb-oterm e))
    (emb-Id-wk1-wk1 A x)
  where
  emb-Id-wk1-wk1 : ∀ A x →
    emb-oterm (O.Id (O.wk1 A) (O.var 0) (O.wk1 x)) PE.≡
    Id (wk1 (emb-oterm A)) (var 0) (wk1 (emb-oterm x))
  emb-Id-wk1-wk1 A x =
    PE.trans (emb-Id (O.wk1 A) (O.var 0) (O.wk1 x))
      (PE.cong₂ (λ a b → Id a (var 0) b) (emb-wk1 A) (emb-wk1 x))

-- Helpers for embedding fst∘wk1 and Univ
emb-fst-wk1 : ∀ e → emb-oterm (O.fst (O.wk1 e)) PE.≡ fst (wk1 (emb-oterm e))
emb-fst-wk1 e = PE.trans (emb-fst (O.wk1 e)) (PE.cong fst (emb-wk1 e))

emb-Univ : ∀ r → emb-oterm (O.gen (O.Ukind r ⁰) []) PE.≡ Univ r ⁰
emb-Univ r = PE.refl

-- Embedding of the cast expression used as the substitution argument in snd and cast-Π
emb-cast-arg : ∀ {A A' rA e} l →
  emb-oterm (O.cast l (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0)) PE.≡
  cast l (wk1 (emb-oterm A')) (wk1 (emb-oterm A))
    (Idsym (Univ rA ⁰) (wk1 (emb-oterm A)) (wk1 (emb-oterm A')) (fst (wk1 (emb-oterm e))))
    (var 0)
emb-cast-arg {A} {A'} {rA} {e} l =
  let oId = O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))
      pId = PE.trans (emb-Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e)))
                (PE.trans (PE.cong (λ u → Idsym u (emb-oterm (O.wk1 A)) (emb-oterm (O.wk1 A'))
                                    (emb-oterm (O.fst (O.wk1 e)))) (emb-Univ rA))
                  (PE.trans (PE.cong (λ x → Idsym (Univ rA ⁰) x (emb-oterm (O.wk1 A'))
                                      (emb-oterm (O.fst (O.wk1 e)))) (emb-wk1 A))
                    (PE.trans (PE.cong (λ y → Idsym (Univ rA ⁰) (wk1 (emb-oterm A)) y
                                        (emb-oterm (O.fst (O.wk1 e)))) (emb-wk1 A'))
                      (PE.cong (λ t → Idsym (Univ rA ⁰) (wk1 (emb-oterm A)) (wk1 (emb-oterm A')) t)
                        (emb-fst-wk1 e)))))
  in  PE.trans (emb-cast l (O.wk1 A') (O.wk1 A) oId (O.var 0))
       (PE.trans (PE.cong (λ a → cast l a (emb-oterm (O.wk1 A)) (emb-oterm oId) (var 0)) (emb-wk1 A'))
         (PE.trans (PE.cong (λ b → cast l (wk1 (emb-oterm A')) b (emb-oterm oId) (var 0)) (emb-wk1 A))
           (PE.cong (λ t → cast l (wk1 (emb-oterm A')) (wk1 (emb-oterm A)) t (var 0)) pId)))

-- Embedding of (snd (wk1 e)) ∘ (var 0)
emb-snd-wk1-∘var : ∀ e l →
  emb-oterm ((O.snd (O.wk1 e)) O.∘ (O.var 0) ^ l) PE.≡
  (snd (wk1 (emb-oterm e))) ∘ (var 0) ^ l
emb-snd-wk1-∘var e l =
  PE.trans (emb-∘ (O.snd (O.wk1 e)) (O.var 0) l)
    (PE.cong (λ t → t ∘ var 0 ^ l)
      (PE.trans (emb-snd (O.wk1 e)) (PE.cong snd (emb-wk1 e))))

emb-snd-subst : ∀ {A A' rA B e} →
  emb-oterm (B O.[ O.cast ⁰ (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
  PE.≡
  emb-oterm B [ cast ⁰ (wk1 (emb-oterm A')) (wk1 (emb-oterm A))
    (Idsym (Univ rA ⁰) (wk1 (emb-oterm A)) (wk1 (emb-oterm A')) (fst (wk1 (emb-oterm e))))
    (var 0) ]↑
emb-snd-subst {A} {A'} {rA} {B} {e} =
  PE.trans (emb-liftSubst B (O.cast ⁰ (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0)))
    (PE.cong (λ t → emb-oterm B [ t ]↑) (emb-cast-arg {A} {A'} {rA} {e} ⁰))

-- Embedding of (wk1 f) ∘ a
emb-wk1-∘a : ∀ {A A' rA e} f l →
  emb-oterm ((O.wk1 f) O.∘
    (O.cast l (O.wk1 A') (O.wk1 A)
      (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0))
    ^ l)
  PE.≡
  (wk1 (emb-oterm f)) ∘
    (cast l (wk1 (emb-oterm A')) (wk1 (emb-oterm A))
      (Idsym (Univ rA ⁰) (wk1 (emb-oterm A)) (wk1 (emb-oterm A')) (fst (wk1 (emb-oterm e))))
      (var 0))
    ^ l
emb-wk1-∘a {A} {A'} {rA} {e} f l =
  PE.trans (emb-∘ (O.wk1 f) _ l)
    (PE.cong₂ (λ t u → t ∘ u ^ l) (emb-wk1 f) (emb-cast-arg {A} {A'} {rA} {e} l))

-- Embedding of the lam body in the cast-Π equality rule
emb-castΠ-lamBody : ∀ {A A' rA B B' e f} → let l = ⁰ in
  let aₜ = cast l (wk1 (emb-oterm A')) (wk1 (emb-oterm A))
              (Idsym (Univ rA l) (wk1 (emb-oterm A)) (wk1 (emb-oterm A'))
                (fst (wk1 (emb-oterm e))))
              (var 0)
  in
  emb-oterm (O.lam A' ▹ O.cast l (B O.[ O.cast l (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
    B' ((O.snd (O.wk1 e)) O.∘ (O.var 0) ^ l)
    ((O.wk1 f) O.∘ O.cast l (O.wk1 A') (O.wk1 A)
      (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ^ l)
    ^ l)
  PE.≡
  lam (emb-oterm A') ▹ cast l (emb-oterm B [ aₜ ]↑) (emb-oterm B')
      ((snd (wk1 (emb-oterm e))) ∘ (var 0) ^ l)
      ((wk1 (emb-oterm f)) ∘ aₜ ^ l)
    ^ l
emb-castΠ-lamBody {A} {A'} {rA} {B} {B'} {e} {f} = body
  where
  l = ⁰
  body : emb-oterm (O.lam A' ▹ O.cast l (B O.[ O.cast l (O.wk1 A') (O.wk1 A)
          (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
          B' ((O.snd (O.wk1 e)) O.∘ (O.var 0) ^ l)
          ((O.wk1 f) O.∘ O.cast l (O.wk1 A') (O.wk1 A)
            (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ^ l)
          ^ l)
        PE.≡
        lam (emb-oterm A') ▹ cast l (emb-oterm B [
          cast l (wk1 (emb-oterm A')) (wk1 (emb-oterm A))
            (Idsym (Univ rA l) (wk1 (emb-oterm A)) (wk1 (emb-oterm A'))
              (fst (wk1 (emb-oterm e))))
            (var 0) ]↑) (emb-oterm B')
          ((snd (wk1 (emb-oterm e))) ∘ (var 0) ^ l)
          ((wk1 (emb-oterm f)) ∘ cast l (wk1 (emb-oterm A')) (wk1 (emb-oterm A))
            (Idsym (Univ rA l) (wk1 (emb-oterm A)) (wk1 (emb-oterm A'))
              (fst (wk1 (emb-oterm e))))
            (var 0) ^ l)
          ^ l
  body = PE.cong (lam (emb-oterm A') ▹_^ l)
           (PE.cong₄ (cast l)
             (emb-snd-subst {A} {A'} {rA} {B} {e})
             PE.refl
             (emb-snd-wk1-∘var e l)
             (emb-wk1-∘a {A} {A'} {rA} {e} f l))

emb-snd-Π-type : ∀ {A A' rA B B'} e →
  (Π (emb-oterm A') ^ rA ° ⁰ ▹ Id (U ⁰)
    (emb-oterm B [ cast ⁰ (wk1 (emb-oterm A')) (wk1 (emb-oterm A))
      (Idsym (Univ rA ⁰) (wk1 (emb-oterm A)) (wk1 (emb-oterm A'))
        (fst (wk1 (emb-oterm e)))) (var 0) ]↑)
    (emb-oterm B') ° ⁰ ° ⁰ ^ %)
  PE.≡
  (emb-oterm (O.Π A' ^ rA ° ⁰ ▹ O.Id (O.U ⁰)
    (B O.[ O.cast ⁰ (O.wk1 A') (O.wk1 A)
      (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
    B' ° ⁰ ° ⁰ ^ %))
emb-snd-Π-type {A} {A'} {rA} {B} {B'} e =
  PE.cong (λ D → (Π (emb-oterm A') ^ rA ° ⁰ ▹ D ° ⁰ ° ⁰ ^ %))
    (PE.cong (λ u → (Id (U ⁰) u (emb-oterm B')))
      (PE.sym (emb-snd-subst {A} {A'} {rA} {B} {e})))
