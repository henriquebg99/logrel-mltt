import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.Canonicity (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Weakening senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.EqRelInstance senv equivs
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.Irrelevance senv equivs
open import Definition.LogicalRelation.ShapeView senv equivs
open import Definition.LogicalRelation.Fundamental.Reducibility senv swf equivs
open import Tools.Empty
open import Tools.Nat
open import Tools.Product
-- Turns a natural number into its term representation
sucᵏ : Nat → Term
sucᵏ 0 = zero
sucᵏ (1+ n) = suc (sucᵏ n)

-- No neutral terms are well-formed in an empty context

-- we need to postulate consistency
-- as we have several uninhabited propositions, we build an predicate
-- to characterize them

-- Note that we could also have defined reductions to Empty of other
-- forms of unihabited types

data isFalse : Term → Set where
  isEmpty : ∀ {lEmpty} → isFalse (Empty lEmpty)
  isIdℕΠ : ∀ {r A rA B r'} → isFalse (Id (Univ r ⁰) ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ r'))
  isIdΠℕ : ∀ {r A rA B r'} → isFalse (Id (Univ r ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ r') ℕ)
  isIdIndΠ : ∀ {r i A rA B r'} → isFalse (Id (Univ r ⁰) (Ind i) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ r'))
  isIdΠInd : ∀ {r i A rA B r'} → isFalse (Id (Univ r ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ r') (Ind i))
  isIdIndℕ : ∀ {r i} → isFalse (Id (Univ r ⁰) (Ind i) ℕ)
  isIdℕInd : ∀ {r i} → isFalse (Id (Univ r ⁰) ℕ (Ind i))
  isIdΠΠ%! : ∀ {r A B A' B' r' r''} → isFalse (Id (Univ r ⁰) (Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰ ^ r') (Π A' ^ ! ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ r''))
  isIdΠΠ!% : ∀ {r A B A' B' r' r''} → isFalse (Id (Univ r ⁰) (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰ ^ r') (Π A' ^ % ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ r''))

consistency = ∀ {t A l} → isFalse A → ε ⊢ t ∷ A ^ [ % , l ] → ⊥

noNe : ∀ {t A r} → consistency → ε ⊢ t ∷ A ^ r → Neutral t → ⊥

-- impossible cases thanks to consistency
noNe consistency (Emptyrecⱼ A ⊢e) Emptyrecₙ = consistency isEmpty ⊢e
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castℕΠₙ = consistency isIdℕΠ [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠℕₙ = consistency isIdΠℕ [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castIndΠₙ = consistency isIdIndΠ [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠIndₙ = consistency isIdΠInd [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castIndℕₙ = consistency isIdIndℕ [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castℕIndₙ = consistency isIdℕInd [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ%!ₙ = consistency isIdΠΠ%! [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ!%ₙ = consistency isIdΠΠ!% [A]₂

-- possible cases proven by induction 
noNe consistency (_ ▹ _ ▹ _ ▹ ⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe consistency  ⊢t neT
noNe consistency (natrecⱼ x _ ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe consistency ⊢t₂ neT
noNe consistency (IndRectⱼ _ _ _ ⊢t _) (IndRectₙ neT) = noNe consistency ⊢t neT
noNe consistency (var x₁ ()) (var x)
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castₙ neT _ _) = noNe consistency [A] neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕₙ neT) = noNe consistency [A]₁ neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castΠₙ neT) = noNe consistency [A]₁ neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕℕₙ neT) = noNe consistency [A]₃ neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castnℕₙ neT) = noNe consistency [A] neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castnΠₙ neT) = noNe consistency [A] neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castnIndₙ neT) = noNe consistency [A] neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castIndₙ neT) = noNe consistency [A]₁ neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castIndIndₙ neT) = noNe consistency [A]₃ neT
noNe consistency (conv ⊢t x) (var n) = noNe consistency ⊢t (var n)
noNe consistency (conv ⊢t x) (∘ₙ neT) = noNe consistency ⊢t (∘ₙ neT)
noNe consistency (conv ⊢t x) (natrecₙ neT) = noNe consistency ⊢t (natrecₙ neT)
noNe consistency (conv ⊢t x) (IndRectₙ neT) = noNe consistency ⊢t (IndRectₙ neT)
noNe consistency (conv ⊢t x) (castₙ neT neT' net) = noNe consistency ⊢t (castₙ neT neT' net)
noNe consistency (conv ⊢t x) (castℕₙ neT) = noNe consistency ⊢t (castℕₙ neT)
noNe consistency (conv ⊢t x) (castΠₙ neT) = noNe consistency ⊢t (castΠₙ neT)
noNe consistency (conv ⊢t x) (castℕℕₙ neT) = noNe consistency ⊢t (castℕℕₙ neT)
noNe consistency (conv ⊢t x) (castnℕₙ neT) = noNe consistency ⊢t (castnℕₙ neT)
noNe consistency (conv ⊢t x) (castnΠₙ neT) = noNe consistency ⊢t (castnΠₙ neT)
noNe consistency (conv ⊢t x) (castnIndₙ neT) = noNe consistency ⊢t (castnIndₙ neT)
noNe consistency (conv ⊢t x) (castIndₙ neT) = noNe consistency ⊢t (castIndₙ neT)
noNe consistency (conv ⊢t x) (castIndIndₙ neT) = noNe consistency ⊢t (castIndIndₙ neT)
noNe consistency (conv ⊢t x) castℕΠₙ = noNe consistency ⊢t castℕΠₙ
noNe consistency (conv ⊢t x) castΠℕₙ = noNe consistency ⊢t castΠℕₙ
noNe consistency (conv ⊢t x) castIndΠₙ = noNe consistency ⊢t castIndΠₙ
noNe consistency (conv ⊢t x) castΠIndₙ = noNe consistency ⊢t castΠIndₙ
noNe consistency (conv ⊢t x) castIndℕₙ = noNe consistency ⊢t castIndℕₙ
noNe consistency (conv ⊢t x) castℕIndₙ = noNe consistency ⊢t castℕIndₙ
noNe consistency (conv ⊢t x) castΠΠ%!ₙ = noNe consistency ⊢t castΠΠ%!ₙ
noNe consistency (conv ⊢t x) castΠΠ!%ₙ = noNe consistency ⊢t castΠΠ!%ₙ
noNe consistency (conv ⊢t x) Emptyrecₙ = noNe consistency ⊢t Emptyrecₙ

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → consistency
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity″ consistency (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ consistency prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ consistency zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ consistency (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe consistency ⊢k neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
              → consistency
              → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
              → ε ⊩⟨ l ⟩ t ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity′ consistency (noemb [ℕ]) (ℕₜ n d n≡n prop) = let a , b = canonicity″ consistency prop
                                          in  a , trans (subset*Term (redₜ d)) b
canonicity′ consistency (emb emb< [ℕ]) [t] = canonicity′ consistency [ℕ] [t]
canonicity′ consistency (emb ∞< [ℕ]) [t] = canonicity′ consistency [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} →
              consistency →
              ε ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ] →
              ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity consistency ⊢t with reducibleTerm ⊢t
canonicity consistency ⊢t | [ℕ] , [t] =
  canonicity′ consistency (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])
