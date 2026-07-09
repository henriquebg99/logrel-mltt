-- Raw terms, weakening (renaming) and substitution.

module Definition.Untyped where

open import Tools.Nat
open import Tools.Product
open import Tools.List
import Tools.PropositionalEquality as PE
open import Definition.Sort public
import Definition.OUntyped as O
OTerm = O.Term
OKind = O.Kind

infix 30 Π_^_°_▹_°_°_^_
infixr 22 _^_°_▹▹_°_°_^_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑

data Kind : Set where
  Ukind : Relevance → Level → Kind
  Pikind : Relevance → Level → Level → Level → Relevance → Kind
  Natkind : Kind
  Lamkind : Level → Kind
  Appkind : Level → Kind
  Zerokind : Kind
  Suckind : Kind
  Natreckind : Level → Kind
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
  Equivkind : Kind -- Equivalence witness
  Nat2kind : Kind  -- 2nd type of natural numbers
  Zero2kind : Kind -- 2nd zero
  Suc2kind : Kind  -- 2nd successor
  Natrec2kind : Level → Kind -- 2nd natural number recursor

data Term : Set where
  var : (x : Nat) → Term
  gen : (k : Kind) (c : List (GenT Term)) → Term

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, ∃ , transp and natrec are binders.

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

-- Natural numbers
ℕ      : Term
ℕ = gen Natkind []

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

-- Introduction and elimination of natural numbers.
zero   : Term                     -- Natural number zero.
zero = gen Zerokind []

suc    : (t : Term)       → Term  -- Successor.
suc t = gen Suckind (⟦ 0 , t ⟧ ∷ [])

natrec : (l : Level) (A t u v : Term) → Term  -- Recursor (A is a binder).
natrec l A t u v = gen (Natreckind l) (⟦ 1 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ ⟦ 0 , v ⟧ ∷ [])

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
equiv-eq : Term
equiv-eq = gen Equivkind []

-- 2nd type of natural numbers
ℕ2      : Term
ℕ2 = gen Nat2kind []

-- Introduction and elimination of 2nd natural numbers.
zero2   : Term                     -- 2nd natural number zero.
zero2 = gen Zero2kind []

suc2    : (t : Term)       → Term  -- 2nd successor.
suc2 t = gen Suc2kind (⟦ 0 , t ⟧ ∷ [])

natrec2 : (l : Level) (A t u v : Term) → Term  -- 2nd natural number recursor (A is a binder).
natrec2 l A t u v = gen (Natrec2kind l) (⟦ 1 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ ⟦ 0 , v ⟧ ∷ [])

------------------------------------------------------------------------
-- Embedding of OTerms into Terms

emb_okind_kind : OKind → Kind
emb_okind_kind (O.Ukind r l) = Ukind r l
emb_okind_kind (O.Pikind r lA lB lΠ rΠ) = Pikind r lA lB lΠ rΠ
emb_okind_kind O.Natkind = Natkind
emb_okind_kind (O.Lamkind l) = Lamkind l
emb_okind_kind (O.Appkind l) = Appkind l
emb_okind_kind O.Zerokind = Zerokind
emb_okind_kind O.Suckind = Suckind
emb_okind_kind (O.Natreckind l) = Natreckind l
emb_okind_kind (O.Emptykind l) = Emptykind l
emb_okind_kind (O.Emptyreckind l lEmpty) = Emptyreckind l lEmpty
emb_okind_kind O.Idkind = Idkind
emb_okind_kind O.Idreflkind = Idreflkind
emb_okind_kind O.Idpikind = Idpikind
emb_okind_kind O.Idspropkind = Idspropkind
emb_okind_kind O.Transpkind = Transpkind
emb_okind_kind (O.Castkind l) = Castkind l
emb_okind_kind O.Castreflkind = Castreflkind
emb_okind_kind O.Fstkind = Fstkind
emb_okind_kind O.Sndkind = Sndkind
emb_okind_kind O.Nat2kind = Nat2kind
emb_okind_kind O.Zero2kind = Zero2kind
emb_okind_kind O.Suc2kind = Suc2kind
emb_okind_kind (O.Natrec2kind l) = Natrec2kind l

mutual
  emb_otermGen : List (GenT OTerm) → List (GenT Term)
  emb_otermGen [] = []
  emb_otermGen (⟦ l , t ⟧ ∷ gs) = ⟦ l , emb_oterm_term t ⟧ ∷ emb_otermGen gs

  emb_oterm_term : OTerm → Term
  emb_oterm_term (O.var x) = var x
  emb_oterm_term (O.gen k gs) = gen (emb_okind_kind k) (emb_otermGen gs)

emb_con : Con OTerm → Con Term
emb_con ε = ε
emb_con (Γ ∙ A ^ r) = emb_con Γ ∙ emb_oterm_term A ^ r

-- Injectivity of term constructors w.r.t. propositional equality.

-- If  Π F G = Π H E  then  F = H  and  G = E.

Π-PE-injectivity : ∀ {F rF lF G lG lΠ r H rH lH E lE lΠ' r'} → Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r PE.≡ Π H ^ rH ° lH ▹ E ° lE ° lΠ' ^ r'
  → F PE.≡ H × rF PE.≡ rH × lF PE.≡ lH × G PE.≡ E × lG PE.≡ lE × lΠ PE.≡ lΠ' × r PE.≡ r'
Π-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

Id-PE-injectivity : ∀ {F G t u t' u'} → Id F t u PE.≡ Id G t' u'
  → F PE.≡ G × t PE.≡ t' × u PE.≡ u'
Id-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : ∀ {n m} → suc n PE.≡ suc m → n PE.≡ m
suc-PE-injectivity PE.refl = PE.refl

suc2-PE-injectivity : ∀ {n m} → suc2 n PE.≡ suc2 m → n PE.≡ m
suc2-PE-injectivity PE.refl = PE.refl

Univ-PE-injectivity : ∀ {r r' l l'} → Univ r l PE.≡ Univ r' l' → r PE.≡ r' × l PE.≡ l'
Univ-PE-injectivity PE.refl = PE.refl , PE.refl

-- Neutral terms.

-- A term is neutral if
-- either it has a variable in head position that blocks reduction.
-- either it is of the form Emptyrec (or terms that should reduce to emptyrec, such as incompatible casts)

data Neutral : Term → Set where
  var     : ∀ n                     → Neutral (var n)
  ∘ₙ      : ∀ {k u l}     → Neutral k → Neutral (k ∘ u ^ l)
  natrecₙ : ∀ {l C c g k} → Neutral k → Neutral (natrec l C c g k)
  castₙ : ∀ {l A B e t} → Neutral A → Neutral B → Neutral t → Neutral (cast l A B e t)
  castnℕₙ : ∀ {l B e t} → Neutral B → Neutral (cast l B ℕ e t)
  castnΠₙ : ∀ {l A rA lA P lP r B e t} → Neutral B → Neutral (cast l B (Π A ^ rA ° lA ▹ P ° lP ° l ^ r) e t)
  castℕₙ : ∀ {l B e t} → Neutral B → Neutral (cast l ℕ B e t)
  castΠₙ : ∀ {l A rA lA P lP r B e t} → Neutral B → Neutral (cast l (Π A ^ rA ° lA ▹ P ° lP ° l ^ r) B e t)
  castℕℕₙ : ∀ {l e t} → Neutral t → Neutral (cast l ℕ ℕ e t)
  castnℕ2ₙ : ∀ {l B e t} → Neutral B → Neutral (cast l B ℕ2 e t)
  castℕ2ₙ : ∀ {l B e t} → Neutral B → Neutral (cast l ℕ2 B e t)
  castℕ2ℕ2ₙ : ∀ {l e t} → Neutral t → Neutral (cast l ℕ2 ℕ2 e t)
  castℕΠₙ : ∀ {l A rA r B e t} → Neutral (cast l ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ r) e t)
  castΠℕₙ : ∀ {l A rA r B e t} → Neutral (cast l (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ r) ℕ e t)
  castℕ2Πₙ : ∀ {l A rA r B e t} → Neutral (cast l ℕ2 (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ r) e t)
  castΠℕ2ₙ : ∀ {l A rA r B e t} → Neutral (cast l (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ r) ℕ2 e t)
  castΠΠ%!ₙ : ∀ {l A B A' B' r r' e t} → Neutral (cast l (Π A ^ % ° ⁰ ▹ B ° ⁰ ° l ^ r) (Π A' ^ ! ° ⁰ ▹ B' ° ⁰ ° l ^ r') e t)
  castΠΠ!%ₙ : ∀ {l A B A' B' r r' e t} → Neutral (cast l (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° l ^ r) (Π A' ^ % ° ⁰ ▹ B' ° ⁰ ° l ^ r') e t)
  Emptyrecₙ : ∀ {l lEmpty A e} -> Neutral (Emptyrec l lEmpty A e)
  natrec2ₙ : ∀ {l C c g k} → Neutral k → Neutral (natrec2 l C c g k)

-- Weak head normal forms (whnfs).
-- These are the (lazy) values of our language.

data Whnf : Term → Set where

  -- Type constructors are whnfs.
  Uₙ    : ∀ {r l} → Whnf (Univ r l)
  Πₙ    : ∀ {A r lA B lB l r'} → Whnf (Π A ^ r ° lA ▹ B ° lB ° l ^ r')
  Idₙ : ∀ {A t u} → Whnf (Id A t u)
  ℕₙ    : Whnf ℕ
  ℕ2ₙ    : Whnf ℕ2
  Emptyₙ : ∀ {l} → Whnf (Empty l)

  -- Introductions are whnfs.
  lamₙ  : ∀ {A t l} → Whnf (lam A ▹ t ^ l)
  zeroₙ : Whnf zero
  sucₙ  : ∀ {t} → Whnf (suc t)
  zero2ₙ : Whnf zero2
  suc2ₙ  : ∀ {t} → Whnf (suc2 t)

  -- Neutrals are whnfs.
  ne   : ∀ {n} → Neutral n → Whnf n


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ℕ : ∀ {r l} → Univ r l PE.≢ ℕ
U≢ℕ ()

U≢ℕ2 : ∀ {r l} → Univ r l PE.≢ ℕ2
U≢ℕ2 ()

U≢Empty : ∀ {r l l'} → Univ r l PE.≢ Empty l'
U≢Empty ()

U≢Π : ∀ {r r' r'' l F lF G lG l'} → Univ r l PE.≢ Π F ^ r' ° lF ▹ G ° lG ° l' ^ r''
U≢Π ()

U≢Id : ∀ {r l F t u} → Univ r l PE.≢ Id F t u
U≢Id ()

U≢ne : ∀ {r l K} → Neutral K → Univ r l PE.≢ K
U≢ne () PE.refl

ℕ≢Π : ∀ {F r lF G lG l r'} → ℕ PE.≢ Π F ^ r ° lF ▹ G ° lG ° l ^ r'
ℕ≢Π ()

ℕ≢Id : ∀ {F t u} → ℕ PE.≢ Id F t u
ℕ≢Id ()

ℕ≢Empty : ∀ {l} → ℕ PE.≢ Empty l
ℕ≢Empty ()

Empty≢ℕ : ∀ {l} → Empty l PE.≢ ℕ
Empty≢ℕ ()

ℕ≢ℕ2 : ℕ PE.≢ ℕ2
ℕ≢ℕ2 ()

Empty≢ℕ2 : ∀ {l} → Empty l PE.≢ ℕ2
Empty≢ℕ2 ()

ℕ2≢Π : ∀ {F r lF G lG l r'} → ℕ2 PE.≢ Π F ^ r ° lF ▹ G ° lG ° l ^ r'
ℕ2≢Π ()

ℕ2≢Id : ∀ {F t u} → ℕ2 PE.≢ Id F t u
ℕ2≢Id ()

ℕ2≢Empty : ∀ {l} → ℕ2 PE.≢ Empty l
ℕ2≢Empty ()

ℕ2≢ℕ : ℕ2 PE.≢ ℕ
ℕ2≢ℕ ()

ℕ≢ne : ∀ {K} → Neutral K → ℕ PE.≢ K
ℕ≢ne () PE.refl

ℕ2≢ne : ∀ {K} → Neutral K → ℕ2 PE.≢ K
ℕ2≢ne () PE.refl

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

zero≢suc : ∀ {n} → zero PE.≢ suc n
zero≢suc ()

zero≢ne : ∀ {k} → Neutral k → zero PE.≢ k
zero≢ne () PE.refl

suc≢ne : ∀ {n k} → Neutral k → suc n PE.≢ k
suc≢ne () PE.refl

zero2≢suc2 : ∀ {n} → zero2 PE.≢ suc2 n
zero2≢suc2 ()

zero2≢ne : ∀ {k} → Neutral k → zero2 PE.≢ k
zero2≢ne () PE.refl

suc2≢ne : ∀ {n k} → Neutral k → suc2 n PE.≢ k
suc2≢ne () PE.refl

zero≢zero2 : zero PE.≢ zero2
zero≢zero2 ()

zero≢suc2 : ∀ {n} → zero PE.≢ suc2 n
zero≢suc2 ()

suc≢zero2 : ∀ {n} → suc n PE.≢ zero2
suc≢zero2 ()

suc≢suc2 : ∀ {n} → suc n PE.≢ suc2 n
suc≢suc2 ()


-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural : Term → Set where
  zeroₙ :                     Natural zero
  sucₙ  : ∀ {t}             → Natural (suc t)
  ne    : ∀ {n} → Neutral n → Natural n

data Natural2 : Term → Set where
  zero2ₙ :                     Natural2 zero2 
  suc2ₙ  : ∀ {t}             → Natural2 (suc2 t)
  ne2    : ∀ {n} → Neutral n → Natural2 n


-- A type in whnf is either Π A B, ℕ, or neutral.
-- Large types could also be U.

data Type : Term → Set where
  Πₙ : ∀ {A r lA B lB l r'} → Type (Π A ^ r ° lA ▹ B ° lB ° l ^ r')
  ℕₙ : Type ℕ
  ℕ2ₙ : Type ℕ2
  Uₙ : ∀ {r l} → Type (Univ r l)
  Emptyₙ : ∀ {l} → Type (Empty l)
  Idₙ : ∀ {A t u} → Type (Id A t u)
  ne : ∀{n} → Neutral n → Type n

-- A whnf of type Π A B is either lam t or neutral.

data Function : Term → Set where
  lamₙ : ∀{A t l} → Function (lam A ▹ t ^ l)
  ne : ∀{n} → Neutral n → Function n

-- These views classify only whnfs.
-- Natural, Type, and Function are a subsets of Whnf.

naturalWhnf : ∀ {n} → Natural n → Whnf n
naturalWhnf sucₙ = sucₙ
naturalWhnf zeroₙ = zeroₙ
naturalWhnf (ne x) = ne x

natural2Whnf : ∀ {n} → Natural2 n → Whnf n
natural2Whnf suc2ₙ = suc2ₙ
natural2Whnf zero2ₙ = zero2ₙ
natural2Whnf (ne2 x) = ne x

typeWhnf : ∀ {A} → Type A → Whnf A
typeWhnf Πₙ = Πₙ
typeWhnf ℕₙ = ℕₙ
typeWhnf Uₙ  = Uₙ
typeWhnf ℕ2ₙ = ℕ2ₙ
typeWhnf Idₙ = Idₙ
typeWhnf Emptyₙ = Emptyₙ
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

-- Weakening of a neutral term.

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n)    = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)    = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n) = natrecₙ (wkNeutral ρ n)
wkNeutral ρ (natrec2ₙ n) = natrec2ₙ (wkNeutral ρ n)
wkNeutral ρ Emptyrecₙ = Emptyrecₙ
wkNeutral ρ (castₙ A B t) = castₙ (wkNeutral ρ A) (wkNeutral ρ B) (wkNeutral ρ t)
wkNeutral ρ (castnℕₙ A) = castnℕₙ (wkNeutral ρ A)
wkNeutral ρ (castnΠₙ A) = castnΠₙ (wkNeutral ρ A)
wkNeutral ρ (castℕₙ A) = castℕₙ (wkNeutral ρ A)
wkNeutral ρ (castΠₙ A) = castΠₙ (wkNeutral ρ A)
wkNeutral ρ (castℕℕₙ t) = castℕℕₙ (wkNeutral ρ t)
wkNeutral ρ (castnℕ2ₙ A) = castnℕ2ₙ (wkNeutral ρ A)
wkNeutral ρ (castℕ2ₙ A) = castℕ2ₙ (wkNeutral ρ A)
wkNeutral ρ (castℕ2ℕ2ₙ t) = castℕ2ℕ2ₙ (wkNeutral ρ t)
wkNeutral ρ castℕΠₙ = castℕΠₙ
wkNeutral ρ castΠℕₙ = castΠℕₙ
wkNeutral ρ castℕ2Πₙ = castℕ2Πₙ
wkNeutral ρ castΠℕ2ₙ = castΠℕ2ₙ
wkNeutral ρ castΠΠ%!ₙ = castΠΠ%!ₙ
wkNeutral ρ castΠΠ!%ₙ = castΠΠ!%ₙ

-- Weakening can be applied to our whnf views.

wkNatural : ∀ {t} ρ → Natural t → Natural (wk ρ t)
wkNatural ρ sucₙ    = sucₙ
wkNatural ρ zeroₙ   = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkNatural2 : ∀ {t} ρ → Natural2 t → Natural2 (wk ρ t)
wkNatural2 ρ suc2ₙ    = suc2ₙ
wkNatural2 ρ zero2ₙ   = zero2ₙ
wkNatural2 ρ (ne2 x) = ne2 (wkNeutral ρ x)

wkType : ∀ {t} ρ → Type t → Type (wk ρ t)
wkType ρ Πₙ      = Πₙ
wkType ρ ℕₙ      = ℕₙ
wkType ρ ℕ2ₙ     = ℕ2ₙ
wkType ρ Uₙ      = Uₙ
wkType ρ Idₙ      = Idₙ
wkType ρ Emptyₙ  = Emptyₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ {t} ρ → Function t → Function (wk ρ t)
wkFunction ρ lamₙ    = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ {t} ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ Idₙ      = Idₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ ℕ2ₙ     = ℕ2ₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ zero2ₙ  = zero2ₙ
wkWhnf ρ suc2ₙ   = suc2ₙ
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)

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

------------------------------------------------------------------------
-- Embedding homomorphism lemmas

emb-substσ : O.Subst → Subst
emb-substσ σ x = emb_oterm_term (σ x)

emb_wk : O.Wk → Wk
emb_wk O.id = id
emb_wk (O.step ρ) = step (emb_wk ρ)
emb_wk (O.lift ρ) = lift (emb_wk ρ)

emb_wk-repeat-lift : ∀ ρ l → emb_wk (O.repeat O.lift ρ l) PE.≡ repeat lift (emb_wk ρ) l
emb_wk-repeat-lift ρ 0 = PE.refl
emb_wk-repeat-lift ρ (1+ l) = PE.cong lift (emb_wk-repeat-lift ρ l)

emb_wkVar : ∀ ρ x → O.wkVar ρ x PE.≡ wkVar (emb_wk ρ) x
emb_wkVar O.id x = PE.refl
emb_wkVar (O.step ρ) x = PE.cong 1+ (emb_wkVar ρ x)
emb_wkVar (O.lift ρ) 0 = PE.refl
emb_wkVar (O.lift ρ) (1+ x) = PE.cong 1+ (emb_wkVar ρ x)

mutual
  emb-wkGen : ∀ ρ gs → emb_otermGen (O.wkGen ρ gs) PE.≡ wkGen (emb_wk ρ) (emb_otermGen gs)
  emb-wkGen ρ [] = PE.refl
  emb-wkGen ρ (⟦ l , t ⟧ ∷ gs) =
    PE.cong₂ _∷_
      (PE.cong (⟦_,_⟧ l)
        (PE.trans (emb-wk (O.repeat O.lift ρ l) t)
          (PE.cong (λ ρ' → wk ρ' (emb_oterm_term t)) (emb_wk-repeat-lift ρ l))))
      (emb-wkGen ρ gs)

  emb-wk : ∀ ρ t → emb_oterm_term (O.wk ρ t) PE.≡ wk (emb_wk ρ) (emb_oterm_term t)
  emb-wk ρ (O.var x) = PE.cong var (emb_wkVar ρ x)
  emb-wk ρ (O.gen k gs) = PE.cong (gen (emb_okind_kind k)) (emb-wkGen ρ gs)

emb-wk1 : ∀ t → emb_oterm_term (O.wk1 t) PE.≡ wk1 (emb_oterm_term t)
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
    emb_otermGen (O.substGen σ gs) PE.≡ substGen σ' (emb_otermGen gs)
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
    emb_oterm_term (O.subst σ t) PE.≡ subst σ' (emb_oterm_term t)
  emb-substσ-eq eq (O.var x) = eq x
  emb-substσ-eq {σ} {σ'} eq (O.gen k gs) =
    PE.cong (gen (emb_okind_kind k)) (emb-substGen-eq eq gs)

  emb-substGen : ∀ σ gs → emb_otermGen (O.substGen σ gs) PE.≡ substGen (emb-substσ σ) (emb_otermGen gs)
  emb-substGen σ [] = PE.refl
  emb-substGen σ (⟦ l , t ⟧ ∷ gs) =
    PE.cong₂ _∷_
      (PE.cong (⟦_,_⟧ l)
        (emb-substσ-eq {σ = O.repeat O.liftSubst σ l}
                       {σ' = repeat liftSubst (emb-substσ σ) l}
                       (emb-substσ-repeat-liftSubst σ l) t))
      (emb-substGen σ gs)

  emb-subst : ∀ (σ : O.Subst) (t : OTerm) →
    emb_oterm_term (O.subst σ t) PE.≡ subst (emb-substσ σ) (emb_oterm_term t)
  emb-subst σ (O.var x) = PE.refl
  emb-subst σ (O.gen k gs) = PE.cong (gen (emb_okind_kind k)) (emb-substGen σ gs)

emb-substσ-wk1Subst : ∀ σ x → emb-substσ (O.wk1Subst σ) x PE.≡ wk1 (emb-substσ σ x)
emb-substσ-wk1Subst σ x = emb-wk1 (σ x)

emb-substσ-consSubst : ∀ σ t x → emb-substσ (O.consSubst σ t) x PE.≡ consSubst (emb-substσ σ) (emb_oterm_term t) x
emb-substσ-consSubst σ t 0 = PE.refl
emb-substσ-consSubst σ t (1+ x) = PE.refl

emb-substσ-consSubst-wk1 : ∀ s n →
  emb-substσ (O.consSubst (O.wk1Subst O.idSubst) s) n
  PE.≡ consSubst (wk1Subst idSubst) (emb_oterm_term s) n
emb-substσ-consSubst-wk1 s 0 = PE.refl
emb-substσ-consSubst-wk1 s (1+ n) = emb-substσ-wk1Subst O.idSubst n

emb-sgSubst : ∀ t s → emb_oterm_term (t O.[ s ]) PE.≡ emb_oterm_term t [ emb_oterm_term s ]
emb-sgSubst t s = emb-substσ-eq (emb-substσ-consSubst O.idSubst s) t

emb-liftSubst : ∀ t s → emb_oterm_term (t O.[ s ]↑) PE.≡ emb_oterm_term t [ emb_oterm_term s ]↑
emb-liftSubst t s = emb-substσ-eq (λ n → emb-substσ-consSubst-wk1 s n) t

emb-Π : ∀ A r lA B lB l r' →
  emb_oterm_term (O.Π A ^ r ° lA ▹ B ° lB ° l ^ r') PE.≡
  Π (emb_oterm_term A) ^ r ° lA ▹ (emb_oterm_term B) ° lB ° l ^ r'
emb-Π A r lA B lB l r' = PE.refl

emb-▹▹ : ∀ A r lA B lB l r' →
  emb_oterm_term (O.Π A ^ r ° lA ▹ O.wk1 B ° lB ° l ^ r') PE.≡
  emb_oterm_term A ^ r ° lA ▹▹ emb_oterm_term B ° lB ° l ^ r'
emb-▹▹ A r lA B lB l r' =
  PE.trans (emb-Π A r lA (O.wk1 B) lB l r')
    (PE.cong (λ T → Π (emb_oterm_term A) ^ r ° lA ▹ T ° lB ° l ^ r') (emb-wk1 B))

emb-sucvar0 : emb_oterm_term (O.suc (O.var Nat.zero)) PE.≡ suc (var Nat.zero)
emb-sucvar0 = PE.refl

emb-suc2var0 : emb_oterm_term (O.suc2 (O.var Nat.zero)) PE.≡ suc2 (var Nat.zero)
emb-suc2var0 = PE.refl

emb-liftSubst-sucvar : ∀ G →
  emb_oterm_term (G O.[ O.suc (O.var Nat.zero) ]↑) PE.≡ emb_oterm_term G [ suc (var Nat.zero) ]↑
emb-liftSubst-sucvar G =
  PE.trans (emb-liftSubst G (O.suc (O.var Nat.zero)))
    (PE.cong (λ t → emb_oterm_term G [ t ]↑) emb-sucvar0)

emb-liftSubst-suc2var : ∀ G →
  emb_oterm_term (G O.[ O.suc2 (O.var Nat.zero) ]↑) PE.≡ emb_oterm_term G [ suc2 (var Nat.zero) ]↑
emb-liftSubst-suc2var G =
  PE.trans (emb-liftSubst G (O.suc2 (O.var Nat.zero)))
    (PE.cong (λ t → emb_oterm_term G [ t ]↑) emb-suc2var0)

emb-wk1-liftSubst : ∀ G s →
  wk1 (emb_oterm_term (G O.[ s ]↑)) PE.≡ wk1 (emb_oterm_term G [ emb_oterm_term s ]↑)
emb-wk1-liftSubst G s = PE.cong wk1 (emb-liftSubst G s)

emb-natrec-inner-s-type : ∀ G rG lG →
  emb_oterm_term (O.natrecStepInner G rG lG) PE.≡
  emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG
emb-natrec-inner-s-type G rG lG =
  PE.trans (emb-▹▹ G rG lG (G O.[ O.suc (O.var Nat.zero) ]↑) lG lG rG)
    (PE.cong (λ B → emb_oterm_term G ^ rG ° lG ▹▹ B ° lG ° lG ^ rG) (emb-liftSubst-sucvar G))

emb-natrec-s-type : ∀ G rG lG →
  emb_oterm_term (O.natrecStepType G rG lG) PE.≡
  Π ℕ ^ ! ° ⁰ ▹ (emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG
emb-natrec-s-type G rG lG =
  PE.trans (emb-Π O.ℕ ! ⁰ (O.natrecStepInner G rG lG) lG lG rG)
    (PE.cong (λ T → Π ℕ ^ ! ° ⁰ ▹ T ° lG ° lG ^ rG) (emb-natrec-inner-s-type G rG lG))

emb-natrec2-inner-s-type : ∀ G rG lG →
  emb_oterm_term (O.natrec2StepInner G rG lG) PE.≡
  emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc2 (var Nat.zero) ]↑ ° lG ° lG ^ rG
emb-natrec2-inner-s-type G rG lG =
  PE.trans (emb-▹▹ G rG lG (G O.[ O.suc2 (O.var Nat.zero) ]↑) lG lG rG)
    (PE.cong (λ B → emb_oterm_term G ^ rG ° lG ▹▹ B ° lG ° lG ^ rG) (emb-liftSubst-suc2var G))

emb-natrec2-s-type : ∀ G rG lG →
  emb_oterm_term (O.natrec2StepType G rG lG) PE.≡
  Π ℕ2 ^ ! ° ⁰ ▹ (emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc2 (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG
emb-natrec2-s-type G rG lG =
  PE.trans (emb-Π O.ℕ2 ! ⁰ (O.natrec2StepInner G rG lG) lG lG rG)
    (PE.cong (λ T → Π ℕ2 ^ ! ° ⁰ ▹ T ° lG ° lG ^ rG) (emb-natrec2-inner-s-type G rG lG))

emb-lam : ∀ A t l →
  emb_oterm_term (O.lam A ▹ t ^ l) PE.≡ lam (emb_oterm_term A) ▹ emb_oterm_term t ^ l
emb-lam A t l = PE.refl

emb-∘ : ∀ t u l →
  emb_oterm_term (t O.∘ u ^ l) PE.≡ emb_oterm_term t ∘ emb_oterm_term u ^ l
emb-∘ t u l = PE.refl

emb-wk1∘var : ∀ f l →
  emb_oterm_term (O.wk1 f O.∘ O.var Nat.zero ^ l) PE.≡
  wk1 (emb_oterm_term f) ∘ var Nat.zero ^ l
emb-wk1∘var f l =
  PE.trans (emb-∘ (O.wk1 f) (O.var Nat.zero) l)
    (PE.cong (λ t → t ∘ var Nat.zero ^ l) (emb-wk1 f))

emb-natrec : ∀ lG G z s n →
  emb_oterm_term (O.natrec lG G z s n) PE.≡
  natrec lG (emb_oterm_term G) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)
emb-natrec lG G z s n = PE.refl

emb-suc : ∀ n → emb_oterm_term (O.suc n) PE.≡ suc (emb_oterm_term n)
emb-suc n = PE.refl

emb-natrec-suc : ∀ l G z s n →
  emb_oterm_term (O.natrec l G z s (O.suc n)) PE.≡
  natrec l (emb_oterm_term G) (emb_oterm_term z) (emb_oterm_term s) (suc (emb_oterm_term n))
emb-natrec-suc l G z s n = PE.refl

emb-natrec-suc-rhs : ∀ l s n G z →
  emb_oterm_term ((s O.∘ n ^ l) O.∘ (O.natrec l G z s n) ^ l) PE.≡
  (emb_oterm_term s ∘ emb_oterm_term n ^ l) ∘ (natrec l (emb_oterm_term G) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)) ^ l
emb-natrec-suc-rhs l s n G z =
  PE.trans (emb-∘ (s O.∘ n ^ l) (O.natrec l G z s n) l)
    (PE.cong (λ t → t ∘ (emb_oterm_term (O.natrec l G z s n)) ^ l) (emb-∘ s n l))

emb-natrec2 : ∀ lG G z s n →
  emb_oterm_term (O.natrec2 lG G z s n) PE.≡
  natrec2 lG (emb_oterm_term G) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)
emb-natrec2 lG G z s n = PE.refl

emb-suc2 : ∀ n → emb_oterm_term (O.suc2 n) PE.≡ suc2 (emb_oterm_term n)
emb-suc2 n = PE.refl

emb-natrec2-suc : ∀ l G z s n →
  emb_oterm_term (O.natrec2 l G z s (O.suc2 n)) PE.≡
  natrec2 l (emb_oterm_term G) (emb_oterm_term z) (emb_oterm_term s) (suc2 (emb_oterm_term n))
emb-natrec2-suc l G z s n = PE.refl

emb-natrec2-suc-rhs : ∀ l s n G z →
  emb_oterm_term ((s O.∘ n ^ l) O.∘ (O.natrec2 l G z s n) ^ l) PE.≡
  (emb_oterm_term s ∘ emb_oterm_term n ^ l) ∘ (natrec2 l (emb_oterm_term G) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)) ^ l
emb-natrec2-suc-rhs l s n G z =
  PE.trans (emb-∘ (s O.∘ n ^ l) (O.natrec2 l G z s n) l)
    (PE.cong (λ t → t ∘ (emb_oterm_term (O.natrec2 l G z s n)) ^ l) (emb-∘ s n l))

emb-cast : ∀ l A B e t →
  emb_oterm_term (O.cast l A B e t) PE.≡
  cast l (emb_oterm_term A) (emb_oterm_term B) (emb_oterm_term e) (emb_oterm_term t)
emb-cast l A B e t = PE.refl

emb-Id : ∀ A t u →
  emb_oterm_term (O.Id A t u) PE.≡ Id (emb_oterm_term A) (emb_oterm_term t) (emb_oterm_term u)
emb-Id A t u = PE.refl

emb-Idrefl : ∀ A t →
  emb_oterm_term (O.Idrefl A t) PE.≡ Idrefl (emb_oterm_term A) (emb_oterm_term t)
emb-Idrefl A t = PE.refl

emb-transp : ∀ A P t s u e →
  emb_oterm_term (O.transp A P t s u e) PE.≡
  transp (emb_oterm_term A) (emb_oterm_term P) (emb_oterm_term t)
         (emb_oterm_term s) (emb_oterm_term u) (emb_oterm_term e)
emb-transp A P t s u e = PE.refl

emb-fst : ∀ e → emb_oterm_term (O.fst e) PE.≡ fst (emb_oterm_term e)
emb-fst e = PE.refl

emb-snd : ∀ e → emb_oterm_term (O.snd e) PE.≡ snd (emb_oterm_term e)
emb-snd e = PE.refl

emb-Emptyrec : ∀ lA A e →
  emb_oterm_term (O.Emptyrec lA ⁰ A e) PE.≡ Emptyrec lA ⁰ (emb_oterm_term A) (emb_oterm_term e)
emb-Emptyrec lA A e = PE.refl

-- Definition of syntaxic sugar

sUnit : Term
sUnit =  Π sEmpty ^ % ° ⁰ ▹ sEmpty ° ⁰ ° ⁰ ^ %

Idsym : (A x y e : Term) → Term
Idsym A x y e = transp A (Id (wk1 A) (var 0) (wk1 x)) x (Idrefl A x) y e

emb-Idsym : ∀ A x y e →
  emb_oterm_term (O.Idsym A x y e) PE.≡
  Idsym (emb_oterm_term A) (emb_oterm_term x) (emb_oterm_term y) (emb_oterm_term e)
emb-Idsym A x y e =
  PE.cong (λ P → transp (emb_oterm_term A) P (emb_oterm_term x)
             (Idrefl (emb_oterm_term A) (emb_oterm_term x))
             (emb_oterm_term y) (emb_oterm_term e))
    (emb-Id-wk1-wk1 A x)
  where
  emb-Id-wk1-wk1 : ∀ A x →
    emb_oterm_term (O.Id (O.wk1 A) (O.var 0) (O.wk1 x)) PE.≡
    Id (wk1 (emb_oterm_term A)) (var 0) (wk1 (emb_oterm_term x))
  emb-Id-wk1-wk1 A x =
    PE.trans (emb-Id (O.wk1 A) (O.var 0) (O.wk1 x))
      (PE.cong₂ (λ a b → Id a (var 0) b) (emb-wk1 A) (emb-wk1 x))

-- Helpers for embedding fst∘wk1 and Univ
emb-fst-wk1 : ∀ e → emb_oterm_term (O.fst (O.wk1 e)) PE.≡ fst (wk1 (emb_oterm_term e))
emb-fst-wk1 e = PE.trans (emb-fst (O.wk1 e)) (PE.cong fst (emb-wk1 e))

emb-Univ : ∀ r → emb_oterm_term (O.gen (O.Ukind r ⁰) []) PE.≡ Univ r ⁰
emb-Univ r = PE.refl

-- Embedding of the cast expression used as the substitution argument in snd and cast-Π
emb-cast-arg : ∀ {A A' rA e} l →
  emb_oterm_term (O.cast l (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0)) PE.≡
  cast l (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A))
    (Idsym (Univ rA ⁰) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A')) (fst (wk1 (emb_oterm_term e))))
    (var 0)
emb-cast-arg {A} {A'} {rA} {e} l =
  let oId = O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))
      pId = PE.trans (emb-Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e)))
                (PE.trans (PE.cong (λ u → Idsym u (emb_oterm_term (O.wk1 A)) (emb_oterm_term (O.wk1 A'))
                                    (emb_oterm_term (O.fst (O.wk1 e)))) (emb-Univ rA))
                  (PE.trans (PE.cong (λ x → Idsym (Univ rA ⁰) x (emb_oterm_term (O.wk1 A'))
                                      (emb_oterm_term (O.fst (O.wk1 e)))) (emb-wk1 A))
                    (PE.trans (PE.cong (λ y → Idsym (Univ rA ⁰) (wk1 (emb_oterm_term A)) y
                                        (emb_oterm_term (O.fst (O.wk1 e)))) (emb-wk1 A'))
                      (PE.cong (λ t → Idsym (Univ rA ⁰) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A')) t)
                        (emb-fst-wk1 e)))))
  in  PE.trans (emb-cast l (O.wk1 A') (O.wk1 A) oId (O.var 0))
       (PE.trans (PE.cong (λ a → cast l a (emb_oterm_term (O.wk1 A)) (emb_oterm_term oId) (var 0)) (emb-wk1 A'))
         (PE.trans (PE.cong (λ b → cast l (wk1 (emb_oterm_term A')) b (emb_oterm_term oId) (var 0)) (emb-wk1 A))
           (PE.cong (λ t → cast l (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A)) t (var 0)) pId)))

-- Embedding of (snd (wk1 e)) ∘ (var 0)
emb-snd-wk1-∘var : ∀ e l →
  emb_oterm_term ((O.snd (O.wk1 e)) O.∘ (O.var 0) ^ l) PE.≡
  (snd (wk1 (emb_oterm_term e))) ∘ (var 0) ^ l
emb-snd-wk1-∘var e l =
  PE.trans (emb-∘ (O.snd (O.wk1 e)) (O.var 0) l)
    (PE.cong (λ t → t ∘ var 0 ^ l)
      (PE.trans (emb-snd (O.wk1 e)) (PE.cong snd (emb-wk1 e))))

emb-snd-subst : ∀ {A A' rA B e} →
  emb_oterm_term (B O.[ O.cast ⁰ (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
  PE.≡
  emb_oterm_term B [ cast ⁰ (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A))
    (Idsym (Univ rA ⁰) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A')) (fst (wk1 (emb_oterm_term e))))
    (var 0) ]↑
emb-snd-subst {A} {A'} {rA} {B} {e} =
  PE.trans (emb-liftSubst B (O.cast ⁰ (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0)))
    (PE.cong (λ t → emb_oterm_term B [ t ]↑) (emb-cast-arg {A} {A'} {rA} {e} ⁰))

-- Embedding of (wk1 f) ∘ a
emb-wk1-∘a : ∀ {A A' rA e} f l →
  emb_oterm_term ((O.wk1 f) O.∘
    (O.cast l (O.wk1 A') (O.wk1 A)
      (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0))
    ^ l)
  PE.≡
  (wk1 (emb_oterm_term f)) ∘
    (cast l (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A))
      (Idsym (Univ rA ⁰) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A')) (fst (wk1 (emb_oterm_term e))))
      (var 0))
    ^ l
emb-wk1-∘a {A} {A'} {rA} {e} f l =
  PE.trans (emb-∘ (O.wk1 f) _ l)
    (PE.cong₂ (λ t u → t ∘ u ^ l) (emb-wk1 f) (emb-cast-arg {A} {A'} {rA} {e} l))

-- Embedding of the lam body in the cast-Π equality rule
emb-castΠ-lamBody : ∀ {A A' rA B B' e f} → let l = ⁰ in
  let aₜ = cast l (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A))
              (Idsym (Univ rA l) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A'))
                (fst (wk1 (emb_oterm_term e))))
              (var 0)
  in
  emb_oterm_term (O.lam A' ▹ O.cast l (B O.[ O.cast l (O.wk1 A') (O.wk1 A)
    (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
    B' ((O.snd (O.wk1 e)) O.∘ (O.var 0) ^ l)
    ((O.wk1 f) O.∘ O.cast l (O.wk1 A') (O.wk1 A)
      (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ^ l)
    ^ l)
  PE.≡
  lam (emb_oterm_term A') ▹ cast l (emb_oterm_term B [ aₜ ]↑) (emb_oterm_term B')
      ((snd (wk1 (emb_oterm_term e))) ∘ (var 0) ^ l)
      ((wk1 (emb_oterm_term f)) ∘ aₜ ^ l)
    ^ l
emb-castΠ-lamBody {A} {A'} {rA} {B} {B'} {e} {f} = body
  where
  l = ⁰
  body : emb_oterm_term (O.lam A' ▹ O.cast l (B O.[ O.cast l (O.wk1 A') (O.wk1 A)
          (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
          B' ((O.snd (O.wk1 e)) O.∘ (O.var 0) ^ l)
          ((O.wk1 f) O.∘ O.cast l (O.wk1 A') (O.wk1 A)
            (O.Idsym (O.gen (O.Ukind rA l) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ^ l)
          ^ l)
        PE.≡
        lam (emb_oterm_term A') ▹ cast l (emb_oterm_term B [
          cast l (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A))
            (Idsym (Univ rA l) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A'))
              (fst (wk1 (emb_oterm_term e))))
            (var 0) ]↑) (emb_oterm_term B')
          ((snd (wk1 (emb_oterm_term e))) ∘ (var 0) ^ l)
          ((wk1 (emb_oterm_term f)) ∘ cast l (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A))
            (Idsym (Univ rA l) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A'))
              (fst (wk1 (emb_oterm_term e))))
            (var 0) ^ l)
          ^ l
  body = PE.cong (lam (emb_oterm_term A') ▹_^ l)
           (PE.cong₄ (cast l)
             (emb-snd-subst {A} {A'} {rA} {B} {e})
             PE.refl
             (emb-snd-wk1-∘var e l)
             (emb-wk1-∘a {A} {A'} {rA} {e} f l))

emb-snd-Π-type : ∀ {A A' rA B B'} e →
  (Π (emb_oterm_term A') ^ rA ° ⁰ ▹ Id (U ⁰)
    (emb_oterm_term B [ cast ⁰ (wk1 (emb_oterm_term A')) (wk1 (emb_oterm_term A))
      (Idsym (Univ rA ⁰) (wk1 (emb_oterm_term A)) (wk1 (emb_oterm_term A'))
        (fst (wk1 (emb_oterm_term e)))) (var 0) ]↑)
    (emb_oterm_term B') ° ⁰ ° ⁰ ^ %)
  PE.≡
  (emb_oterm_term (O.Π A' ^ rA ° ⁰ ▹ O.Id (O.U ⁰)
    (B O.[ O.cast ⁰ (O.wk1 A') (O.wk1 A)
      (O.Idsym (O.gen (O.Ukind rA ⁰) []) (O.wk1 A) (O.wk1 A') (O.fst (O.wk1 e))) (O.var 0) ]↑)
    B' ° ⁰ ° ⁰ ^ %))
emb-snd-Π-type {A} {A'} {rA} {B} {B'} e =
  PE.cong (λ D → (Π (emb_oterm_term A') ^ rA ° ⁰ ▹ D ° ⁰ ° ⁰ ^ %))
    (PE.cong (λ u → (Id (U ⁰) u (emb_oterm_term B')))
      (PE.sym (emb-snd-subst {A} {A'} {rA} {B} {e})))
