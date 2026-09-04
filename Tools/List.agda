{-# OPTIONS --safe #-}

module Tools.List where

open import Tools.Nat
open import Tools.Product
open import Tools.PropositionalEquality

infixr 30 _∷_
infixr 5 _++_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_∷ʳ_ : {A : Set} → List A → A → List A
[]        ∷ʳ y = y ∷ []
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = 1+ (length xs)

length-map : ∀ {A B} (f : A → B) (xs : List A) → length (map f xs) ≡ length xs
length-map f [] = refl
length-map f (x ∷ xs) = cong 1+ (length-map f xs)

zip : {A B : Set} → List A → List B → List (A × B)
zip [] _ = []
zip (_ ∷ _) [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

zip-map : ∀ {A B C} (f : B → C) (xs : List A) (ys : List B) →
  zip xs (map f ys) ≡ map (λ p → (proj₁ p , f (proj₂ p))) (zip xs ys)
zip-map f [] ys = refl
zip-map f (x ∷ xs) [] = refl
zip-map f (x ∷ xs) (y ∷ ys) = cong ((x , f y) ∷_) (zip-map f xs ys)

zip-map-fst : ∀ {A B C} (f : A → C) (xs : List A) (ys : List B) →
  zip (map f xs) ys ≡ map (λ p → (f (proj₁ p) , proj₂ p)) (zip xs ys)
zip-map-fst f [] ys = refl
zip-map-fst f (x ∷ xs) [] = refl
zip-map-fst f (x ∷ xs) (y ∷ ys) = cong ((f x , y) ∷_) (zip-map-fst f xs ys)

replicate : {A : Set} → Nat → A → List A
replicate 0 _ = []
replicate (1+ n) x = x ∷ replicate n x

replicate-snoc : ∀ {A} n (x : A) → replicate n x ∷ʳ x ≡ replicate (1+ n) x
replicate-snoc 0 x = refl
replicate-snoc (1+ n) x = cong (x ∷_) (replicate-snoc n x)

length-replicate : ∀ {A} n (x : A) → length (replicate n x) ≡ n
length-replicate 0 x = refl
length-replicate (1+ n) x = cong 1+ (length-replicate n x)

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr f z [] = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldl : {A B : Set} → (B → A → B) → B → List A → B
foldl f z [] = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

-- [0, 1, …, n − 1]
range : Nat → List Nat
range 0 = []
range (1+ n) = range n ∷ʳ n

map-∷ʳ : ∀ {A B} (f : A → B) xs y →
  map f (xs ∷ʳ y) ≡ map f xs ∷ʳ f y
map-∷ʳ f [] y = refl
map-∷ʳ f (x ∷ xs) y = cong (f x ∷_) (map-∷ʳ f xs y)

range-suc : ∀ n → range (1+ n) ≡ 0 ∷ map 1+ (range n)
range-suc 0 = refl
range-suc (1+ n) =
  trans (cong (_∷ʳ 1+ n) (range-suc n))
    (cong (0 ∷_) (sym (map-∷ʳ 1+ (range n) n)))

length-∷ʳ : ∀ {A} (xs : List A) y → length (xs ∷ʳ y) ≡ 1+ (length xs)
length-∷ʳ [] y = refl
length-∷ʳ (x ∷ xs) y = cong 1+ (length-∷ʳ xs y)

length-range : ∀ n → length (range n) ≡ n
length-range 0 = refl
length-range (1+ n) = trans (length-∷ʳ (range n) n) (cong 1+ (length-range n))

length-zip-eq : ∀ {A B} (xs : List A) (ys : List B) →
  length xs ≡ length ys → length (zip xs ys) ≡ length xs
length-zip-eq [] [] eq = refl
length-zip-eq (x ∷ xs) (y ∷ ys) eq = cong 1+ (length-zip-eq xs ys (cong pred eq))
length-zip-eq [] (y ∷ ys) ()
length-zip-eq (x ∷ xs) [] ()

zip-range-cons : ∀ {A} (a : A) (as : List A) →
  zip (range (1+ (length as))) (a ∷ as) ≡
  (0 , a) ∷ map (λ p → (1+ (proj₁ p) , proj₂ p)) (zip (range (length as)) as)
zip-range-cons {A} a as =
  trans (cong (λ r → zip r (a ∷ as)) (range-suc (length as)))
    (cong ((0 , a) ∷_) (zip-map-fst {A = Nat} {B = A} {C = Nat} (λ n → 1+ n)
      (range (length as)) as))

-- Membership

data _∈ₗ_ {A : Set} : A → List A → Set where
  hereₗ  : ∀ {x xs} → x ∈ₗ (x ∷ xs)
  thereₗ : ∀ {x y xs} → x ∈ₗ xs → x ∈ₗ (y ∷ xs)

∷-inj₁ : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷-inj₁ refl = refl

∷-inj₂ : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-inj₂ refl = refl

map-injective : {A B : Set} {f : A → B} {xs ys : List A} →
  (∀ {x y} → f x ≡ f y → x ≡ y) →
  map f xs ≡ map f ys → xs ≡ ys
map-injective {xs = []} {ys = []} _ _ = refl
map-injective {xs = []} {ys = _ ∷ _} _ ()
map-injective {xs = _ ∷ _} {ys = []} _ ()
map-injective {xs = _ ∷ xs} {ys = _ ∷ ys} inj eq =
  cong₂ _∷_ (inj (∷-inj₁ eq)) (map-injective inj (∷-inj₂ eq))

∈ₗ-map-1+ : ∀ xs x → x ∈ₗ map 1+ xs →
  ∃ λ y → (x ≡ 1+ y) × (y ∈ₗ xs)
∈ₗ-map-1+ [] x ()
∈ₗ-map-1+ (y ∷ xs) .(1+ y) hereₗ = y , refl , hereₗ
∈ₗ-map-1+ (y ∷ xs) x (thereₗ h) with ∈ₗ-map-1+ xs x h
... | y′ , eq′ , inn = y′ , eq′ , thereₗ inn

∈ₗ-range : ∀ m x → x ∈ₗ range m → x << m
∈ₗ-range 0 x ()
∈ₗ-range (1+ m) x h = help (subst (x ∈ₗ_) (range-suc m) h)
  where
  help : x ∈ₗ (0 ∷ map 1+ (range m)) → x << 1+ m
  help hereₗ = leS le0
  help (thereₗ h′) with ∈ₗ-map-1+ (range m) x h′
  ... | y , eq′ , inn =
    subst (_<< 1+ m) (sym eq′) (leS (∈ₗ-range m y inn))

∈ₗ-map-inv : ∀ {A B} (f : A → B) xs y →
  y ∈ₗ map f xs → ∃ λ x → (y ≡ f x) × (x ∈ₗ xs)
∈ₗ-map-inv f [] y ()
∈ₗ-map-inv f (x ∷ xs) .(f x) hereₗ = x , refl , hereₗ
∈ₗ-map-inv f (x ∷ xs) y (thereₗ h) with ∈ₗ-map-inv f xs y h
... | x′ , eq′ , inn = x′ , eq′ , thereₗ inn

zip-∈ₗ : ∀ {A B} (xs : List A) (ys : List B) q →
  q ∈ₗ zip xs ys → (proj₁ q ∈ₗ xs) × (proj₂ q ∈ₗ ys)
zip-∈ₗ [] ys q ()
zip-∈ₗ (_ ∷ xs) [] q ()
zip-∈ₗ (x ∷ xs) (y ∷ ys) .(x , y) hereₗ = hereₗ , hereₗ
zip-∈ₗ (x ∷ xs) (y ∷ ys) q (thereₗ h) with zip-∈ₗ xs ys q h
... | hx , hy = thereₗ hx , thereₗ hy

-- Pointwise predicate on lists
data All {A : Set} (P : A → Set) : List A → Set where
  []ₐ  : All P []
  _∷ₐ_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

data All₂ {A : Set} (P : A → A → Set) : List A → List A → Set where
  []ₐ  : All₂ P [] []
  _∷ₐ_ : ∀ {x y xs ys} → P x y → All₂ P xs ys → All₂ P (x ∷ xs) (y ∷ ys)

data All₃ {A B C : Set} (P : A → B → C → Set) : List A → List B → List C → Set where
  []ₐ  : All₃ P [] [] []
  _∷ₐ_ : ∀ {x y z xs ys zs} → P x y z → All₃ P xs ys zs → All₃ P (x ∷ xs) (y ∷ ys) (z ∷ zs)

all∈ : ∀ {A} {P : A → Set} {xs} → (∀ x → x ∈ₗ xs → P x) → All P xs
all∈ {xs = []} _ = []ₐ
all∈ {xs = x ∷ xs} f = f x hereₗ ∷ₐ all∈ (λ y p → f y (thereₗ p))

mapAll : ∀ {A B} {P : A → Set} {Q : B → Set} (f : A → B)
       → (∀ {x} → P x → Q (f x)) → ∀ {xs} → All P xs → All Q (map f xs)
mapAll f g []ₐ = []ₐ
mapAll f g (p ∷ₐ ps) = g p ∷ₐ mapAll f g ps

mapAll₂ : ∀ {A B} {P : A → A → Set} {Q : B → B → Set} (f : A → B)
        → (∀ {x y} → P x y → Q (f x) (f y))
        → ∀ {xs ys} → All₂ P xs ys → All₂ Q (map f xs) (map f ys)
mapAll₂ f g []ₐ = []ₐ
mapAll₂ f g (p ∷ₐ ps) = g p ∷ₐ mapAll₂ f g ps

All₂-length : ∀ {A} {P : A → A → Set} {xs ys} →
  All₂ P xs ys → length xs ≡ length ys
All₂-length []ₐ = refl
All₂-length (_ ∷ₐ ps) = cong 1+ (All₂-length ps)

map-++ : ∀ {A B} (f : A → B) xs ys →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f [] ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

-- Lookup with default (used when index is known in-range)
lookupDefault : {A : Set} → A → List A → Nat → A
lookupDefault d [] _ = d
lookupDefault d (x ∷ _) 0 = x
lookupDefault d (_ ∷ xs) (1+ n) = lookupDefault d xs n

-- Lookup in an All, given a proof that the index is in range
lookupAll : ∀ {A} {P : A → Set} {xs} (d : A) →
  All P xs → ∀ n → n << length xs → P (lookupDefault d xs n)
lookupAll d []ₐ n ()
lookupAll d (p ∷ₐ _) 0 (leS _) = p
lookupAll d (_ ∷ₐ ps) (1+ n) (leS h) = lookupAll d ps n h

-- Lookup in an All₂, given a proof that the index is in range
lookupAll₂ : ∀ {A} {P : A → A → Set} {xs ys} (dx dy : A) →
  All₂ P xs ys → ∀ n → n << length xs →
  P (lookupDefault dx xs n) (lookupDefault dy ys n)
lookupAll₂ dx dy []ₐ n ()
lookupAll₂ dx dy (p ∷ₐ _) 0 (leS _) = p
lookupAll₂ dx dy (_ ∷ₐ ps) (1+ n) (leS h) = lookupAll₂ dx dy ps n h
