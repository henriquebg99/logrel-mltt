{-# OPTIONS --safe #-}

-- Syntactic facts about the method types of IndRect: their normal form
-- (an argument telescope followed by one induction hypothesis per
-- recursive argument) and the instantiation of their argument binders.

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Untyped.IndRect (senv : SI.SEnv) (equivs : E.Equivs senv) where

open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Tools.Nat
open import Tools.Product
open import Tools.Nullary using (Dec; yes; no)
open import Tools.List using (List; map; length; length-map; range; range-suc; zip; foldr; lookupDefault)
  renaming ([] to []ₗ; _∷_ to _∷ₗ_)
open import Tools.Inequality using (Bool; true; false; eqb; eqb-no; filter)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU
import Definition.OUntyped senv as O

------------------------------------------------------------------------
-- Shape of the constructor-argument list.
-- Every constructor argument has a closed type emb-stype T; the recursive
-- ones (T = Ind i) are listed by ctrRecIndices.

ctrArity : List SU.Type → Nat
ctrArity Ts = length Ts

ctrArgTys : ∀ Ts → map proj₁ (ctrArgsTypeList Ts) PE.≡ map emb-stype Ts
ctrArgTys Ts =
  PE.trans (map-map proj₁ (λ p → (emb-oterm (proj₁ p) , proj₂ p))
                    (O.ctrArgsTypeList Ts))
    (PE.trans (map-map (λ p → emb-oterm (proj₁ p))
                       (λ T → (O.emb-stype-oterm T , 0))
                       Ts)
              (map-cong Ts emb-stype-hom))

eqb-true : ∀ m n → eqb m n PE.≡ true → m PE.≡ n
eqb-true m n eq = decEq-true (m ≟ n)
  where
  decEq-true : Dec (m PE.≡ n) → m PE.≡ n
  decEq-true (yes e) = e
  decEq-true (no m≢n) with PE.trans (PE.sym (eqb-no m n m≢n)) eq
  ... | ()

-- Recursive positions and recursive arguments are filtered alike.
map-ctrRecIndices : ∀ {A : Set} (f : Nat → A) i (ns : List Nat) (Ts : List SU.Type) →
  map f (map proj₁ (filter (λ jT → SU.ctrArgIsRecursive i (proj₂ jT)) (zip ns Ts)))
  PE.≡ map proj₁ (filter (λ aT → SU.ctrArgIsRecursive i (proj₂ aT)) (zip (map f ns) Ts))
map-ctrRecIndices f i []ₗ Ts = PE.refl
map-ctrRecIndices f i (x ∷ₗ ns) []ₗ = PE.refl
map-ctrRecIndices f i (x ∷ₗ ns) (T ∷ₗ Ts) with SU.ctrArgIsRecursive i T
... | true  = PE.cong (f x ∷ₗ_) (map-ctrRecIndices f i ns Ts)
... | false = map-ctrRecIndices f i ns Ts

------------------------------------------------------------------------
-- Arithmetic of the de Bruijn indices of a method type.

plus-minus : ∀ a b v → v <= b → ((a + b) - v) PE.≡ a + (b - v)
plus-minus a b 0 _ = PE.refl
plus-minus a 0 (1+ v) ()
plus-minus a (1+ b) (1+ v) (leS h) =
  PE.trans (PE.cong (λ m → m - (1+ v)) (plusSuc a b)) (plus-minus a b v h)

varIdx : ∀ k n v → v << n → (((k + n) - 1) - v) PE.≡ k + ((n - 1) - v)
varIdx k n v h =
  PE.trans (PE.sym (minus-suc (k + n) v))
    (PE.trans (plus-minus k n (1+ v) h) (PE.cong (_+_ k) (minus-suc n v)))

------------------------------------------------------------------------
-- Telescopes.
-- Both phases of a method type are Π-telescopes built with foldr; the
-- hypothesis phase is in fact a chain of non-dependent arrows.

-- Π former of a telescope step (domain level lD, codomain level lG).
Πt : Level → Level → Term → Term → Term
Πt lD lG A B = Π A ^ ! ° lD ▹ B ° lG ° lG ^ !

-- Iterated non-dependent arrow.
arrows : Level → List Term → Term → Term
arrows lG []ₗ E = E
arrows lG (D ∷ₗ Ds) E = Πt lG lG D (wk1 (arrows lG Ds E))

-- Telescope of hypotheses that do not depend on each other:
-- the p-th entry is weakened p times.
wkTele : List Term → List Term
wkTele []ₗ = []ₗ
wkTele (D ∷ₗ Ds) = D ∷ₗ map wk1 (wkTele Ds)

length-wkTele : ∀ Ds → length (wkTele Ds) PE.≡ length Ds
length-wkTele []ₗ = PE.refl
length-wkTele (D ∷ₗ Ds) =
  PE.cong 1+ (PE.trans (length-map wk1 (wkTele Ds)) (length-wkTele Ds))

-- Weakening of a telescope: the p-th entry is weakened under p lifts.
wkTel : Wk → List Term → List Term
wkTel ρ []ₗ = []ₗ
wkTel ρ (A ∷ₗ As) = wk ρ A ∷ₗ wkTel (lift ρ) As

wk-foldr : ∀ ρ lD lG (L : List Term) Z →
  wk ρ (foldr (Πt lD lG) Z L) PE.≡
  foldr (Πt lD lG) (wk (repeat lift ρ (length L)) Z) (wkTel ρ L)
wk-foldr ρ lD lG []ₗ Z = PE.refl
wk-foldr ρ lD lG (A ∷ₗ L) Z =
  PE.cong (Πt lD lG (wk ρ A))
    (PE.trans (wk-foldr (lift ρ) lD lG L Z)
      (PE.cong (λ ρ′ → foldr (Πt lD lG) (wk ρ′ Z) (wkTel (lift ρ) L))
               (repeat-lift-lift ρ (length L))))

wk1-wk1^ : ∀ p X → wk1^ p (wk1 X) PE.≡ wk1 (wk1^ p X)
wk1-wk1^ 0 X = PE.refl
wk1-wk1^ (1+ p) X = PE.cong wk1 (wk1-wk1^ p X)

wk1^-wk : ∀ p X → wk (repeat lift (step id) p) (wk1^ p X) PE.≡ wk1^ p (wk1 X)
wk1^-wk 0 X = PE.refl
wk1^-wk (1+ p) X =
  PE.trans (PE.sym (wk1-wk≡lift-wk1 (repeat lift (step id) p) (wk1^ p X)))
           (PE.cong wk1 (wk1^-wk p X))

-- Iterated map wk1 over a telescope.
mapwk1^ : Nat → List Term → List Term
mapwk1^ 0 L = L
mapwk1^ (1+ p) L = mapwk1^ p (map wk1 L)

mapwk1^-[] : ∀ p → mapwk1^ p []ₗ PE.≡ []ₗ
mapwk1^-[] 0 = PE.refl
mapwk1^-[] (1+ p) = mapwk1^-[] p

mapwk1^-∷ : ∀ p D L → mapwk1^ p (D ∷ₗ L) PE.≡ wk1^ p D ∷ₗ mapwk1^ p L
mapwk1^-∷ 0 D L = PE.refl
mapwk1^-∷ (1+ p) D L =
  PE.trans (mapwk1^-∷ p (wk1 D) (map wk1 L))
           (PE.cong (_∷ₗ mapwk1^ p (map wk1 L)) (wk1-wk1^ p D))

wkTel-wkTele : ∀ Ds → wkTel (step id) (wkTele Ds) PE.≡ map wk1 (wkTele Ds)
wkTel-wkTele Ds = go 0 Ds
  where
    go : ∀ p Ds → wkTel (repeat lift (step id) p) (mapwk1^ p (wkTele Ds))
                  PE.≡ map wk1 (mapwk1^ p (wkTele Ds))
    go p []ₗ rewrite mapwk1^-[] p = PE.refl
    go p (D ∷ₗ Ds) rewrite mapwk1^-∷ p D (map wk1 (wkTele Ds)) =
      PE.cong₂ _∷ₗ_ (PE.trans (wk1^-wk p D) (wk1-wk1^ p D)) (go (1+ p) Ds)

arrows-foldr : ∀ lG (Ds : List Term) E →
  foldr (Πt lG lG) (wk1^ (length Ds) E) (wkTele Ds) PE.≡ arrows lG Ds E
arrows-foldr lG []ₗ E = PE.refl
arrows-foldr lG (D ∷ₗ Ds) E =
  PE.cong (Πt lG lG D)
    (PE.trans
      (PE.cong₂ (λ Z L → foldr (Πt lG lG) Z L)
        (PE.trans (PE.sym (wk1-wk1^ (length Ds) E))
                  (PE.sym (wk1^-wk (length Ds) E)))
        (PE.sym (wkTel-wkTele Ds)))
      (PE.trans
        (PE.cong (λ m → foldr (Πt lG lG)
                          (wk (repeat lift (step id) m) (wk1^ (length Ds) E))
                          (wkTel (step id) (wkTele Ds)))
                 (PE.sym (length-wkTele Ds)))
        (PE.trans (PE.sym (wk-foldr (step id) lG lG (wkTele Ds) (wk1^ (length Ds) E)))
                  (PE.cong wk1 (arrows-foldr lG Ds E)))))

------------------------------------------------------------------------
-- Instantiation of the argument binders of a method type.

wk1^-plus : ∀ m n X → wk1^ (m + n) X PE.≡ wk1^ m (wk1^ n X)
wk1^-plus 0 n X = PE.refl
wk1^-plus (1+ m) n X = PE.cong wk1 (wk1^-plus m n X)

subst-wk1^ : ∀ n σ t →
  subst (repeat liftSubst σ n) (wk1^ n t) PE.≡ wk1^ n (subst σ t)
subst-wk1^ 0 σ t = PE.refl
subst-wk1^ (1+ n) σ t =
  PE.trans (Idsym-subst-lemma (repeat liftSubst σ n) (wk1^ n t))
           (PE.cong wk1 (subst-wk1^ n σ t))

substVar-lifts-≥ : ∀ n σ y → repeat liftSubst σ n (n + y) PE.≡ wk1^ n (σ y)
substVar-lifts-≥ 0 σ y = PE.refl
substVar-lifts-≥ (1+ n) σ y = PE.cong wk1 (substVar-lifts-≥ n σ y)

-- The substitution instantiating the n argument binders with as.
argSubst : List Term → Subst
argSubst []ₗ = idSubst
argSubst (a ∷ₗ as) = argSubst as ₛ•ₛ repeat liftSubst (sgSubst a) (length as)

argSubst-wk : ∀ as X → subst (argSubst as) (wk1^ (length as) X) PE.≡ X
argSubst-wk []ₗ X = subst-id X
argSubst-wk (a ∷ₗ as) X =
  PE.trans (PE.sym (substCompEq (wk1^ (1+ (length as)) X)))
    (PE.trans
      (PE.cong (subst (argSubst as))
        (PE.trans (PE.cong (subst (repeat liftSubst (sgSubst a) (length as)))
                           (PE.sym (wk1-wk1^ (length as) X)))
          (PE.trans (subst-wk1^ (length as) (sgSubst a) (wk1 X))
                    (PE.cong (wk1^ (length as)) (wk1-singleSubst X a)))))
      (argSubst-wk as X))

argSubst-var : ∀ as p → p << length as →
  subst (argSubst as) (var ((length as - 1) - p)) PE.≡ lookupDefault (var 0) as p
argSubst-var []ₗ p ()
argSubst-var (a ∷ₗ as) 0 (leS _) =
  PE.trans (PE.cong (λ x → subst (argSubst as)
                             (repeat liftSubst (sgSubst a) (length as) x))
                    (PE.sym (plusZero (length as))))
    (PE.trans (PE.cong (subst (argSubst as))
                       (substVar-lifts-≥ (length as) (sgSubst a) 0))
              (argSubst-wk as a))
argSubst-var (a ∷ₗ as) (1+ p) (leS h) =
  PE.trans (PE.cong (λ x → subst (argSubst as)
                             (repeat liftSubst (sgSubst a) (length as) x))
                    (minus-suc (length as) p))
    (PE.trans (PE.cong (subst (argSubst as))
                       (substVar-lifts-< (length as) (sgSubst a)
                          ((length as - 1) - p) (minus-<- (length as) p h)))
              (argSubst-var as p h))

------------------------------------------------------------------------
-- Normal form of a method type once its argument binders are instantiated.
-- Substituting the n arguments collapses the hypothesis phase into the
-- chain of non-dependent arrows (P ∘ a₀) ▹▹ … ▹▹ (P ∘ ctr i j as).

Πarg : Relevance → Level → Term → Term → Term
Πarg rG lG A B = Π A ^ ! ° ⁰ ▹ B ° lG ° lG ^ rG

Πih : Relevance → Level → Term → Term → Term
Πih rG lG A B = Π A ^ rG ° lG ▹ B ° lG ° lG ^ rG

-- The n arguments of the constructor, seen under k hypotheses, and the
-- conclusion of a method type (the hypothesis telescope ihGo is in
-- Definition.Untyped.Properties).
ctrVars : Nat → Nat → List Term
ctrVars n k = map (λ v → var (((k + n) - 1) - v)) (range n)

concl : Nat → Nat → Term → Nat → Nat → Term
concl i j P n k = P [ ctr i j (ctrVars n k) ]↑^ (k + n)

arity≡ : ∀ Ts → length (ctrArgsTypeList Ts) PE.≡ ctrArity Ts
arity≡ Ts =
  PE.trans (length-map (λ p → (emb-oterm (proj₁ p) , proj₂ p))
                       (O.ctrArgsTypeList Ts))
           (length-map (λ T → (O.emb-stype-oterm T , 0)) Ts)

-- Method types are argument telescopes over the (closed) argument types,
-- followed by one induction hypothesis per recursive argument.
branchTy-nf : ∀ i j Ts P rG lG →
  indRectBranchTy i j Ts P rG lG PE.≡
  foldr (Πarg rG lG)
    (foldr (Πih rG lG) (concl i j P (ctrArity Ts) (length (ctrRecIndices i Ts)))
                       (ihGo (ctrArity Ts) P 0 (ctrRecIndices i Ts)))
    (map emb-stype Ts)
branchTy-nf i j Ts P rG lG
  rewrite ctrArgTys Ts | arity≡ Ts =
  PE.cong (λ L → foldr (Πarg rG lG)
                   (foldr (Πih rG lG) (concl i j P (ctrArity Ts) (length (ctrRecIndices i Ts))) L)
                   (map emb-stype Ts))
    (PE.sym (ihGo-range (ctrArity Ts) P (ctrRecIndices i Ts)))

-- Recursive arguments are those at the inductive type being eliminated.
rec-Ind : ∀ i T → SU.ctrArgIsRecursive i T PE.≡ true → T PE.≡ SU.Ind i
rec-Ind i (SU.Ind j) e = PE.cong SU.Ind (eqb-true j i e)
rec-Ind i (SU.Arrow A B) ()
