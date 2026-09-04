open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne; U≢Empty; ℕ≢Empty; Empty≢Π; Empty≢ne; ℕ≢ℕ2; ℕ2≢ℕ)
import Definition.Equiv as E
module Definition.Typed.Consequences.Inequality where
open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne; U≢Empty; ℕ≢Empty; Empty≢Π; Empty≢ne)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Equality
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE
A≢B : ∀ {A B rA rB Γ} (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term → TypeLevel → Term → Set)
      (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A ^ rA)
      (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B ^ rB)
      (A-elim : ∀ {l} → Γ ⊩⟨ l ⟩ A ^ rA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩A A)
      (B-elim : ∀ {l} → Γ ⊩⟨ l ⟩ B ^ rA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩B B)
      (A≢B′ : ∀ {l l′} ([A] : Γ ⊩′⟨ l ⟩A A) ([B] : Γ ⊩′⟨ l′ ⟩B B)
            → ShapeView Γ l l′ A B rA rB (A-intr [A]) (B-intr [B]) → ⊥)
    → Γ ⊢ A ≡ B ^ rA → ⊥
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B =
  let X = reducibleEq A≡B
      [A] = proj₁ X
      [B] = proj₁ (proj₂ X)
      [A≡B] = proj₂ (proj₂ X)
      _ , [A]′ = A-elim ([A])
      _ , [B]′ = B-elim ([B])
      [A≡B]′ = irrelevanceEq [A] (A-intr [A]′) [A≡B]
  in  A≢B′ [A]′ [B]′ (goodCases (A-intr [A]′) (B-intr [B]′) [A≡B]′)


U≢ℕ′ : ∀ {Γ A ll B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ ll)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ [ ! , _ ] [ ! , _ ] (Uᵣ {ll = ll} [U]) (ℕᵣ [ℕ]) → ⊥
U≢ℕ′ a b ()

U≢ℕ-red : ∀ {ll r lU B Γ} → Γ ⊢ B ⇒* ℕ ^ [ ! , ll ] → Γ ⊢ Univ r lU ≡ B ^ [ ! , ll ] → ⊥
U≢ℕ-red {ll} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ll) (λ Γ l B → Γ ⊩ℕ B) Uᵣ ℕᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ-elim′ D x))
                U≢ℕ′

-- U and ℕ cannot be judgmentally equal.
U≢ℕ! : ∀ {r l ll Γ} → Γ ⊢ Univ r l ≡ ℕ ^ [ ! , ll ] → ⊥
U≢ℕ! U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ

-- U vs Pi
U≢Π′ : ∀ {A lA B lB Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ lA)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^[ lB ])
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {ll = lA} [U]) (Πᵣ [Π]) → ⊥
U≢Π′ a b ()

U≢Π-red : ∀ {ll B F G rF lF lG rU lU Γ} → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° lG ° ll ^ ! ^ [ ! , ι ll ]
            → Γ ⊢ Univ rU lU ≡ B ^ [ ! , ι ll ] → ⊥
U≢Π-red {ll} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ι ll)
                (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ ll ]) Uᵣ Πᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Π-elim′ D x))
                U≢Π′

-- U and Π F ▹ G for any F and G cannot be judgmentally equal.
U≢Π! : ∀ {rU lU F rF lF lG G l Γ} → Γ ⊢ Univ rU lU ≡ Π F ^ rF ° lF ▹ G  ° lG ° l ^ ! ^ [ ! , ι l ] → ⊥
U≢Π! U≡Π =
  let _ , ⊢Π = syntacticEq U≡Π
  in  U≢Π-red (id ⊢Π) U≡Π


-- Id vs Pi

Id≢Π′ : ∀ {A B Γ l l′}
       ([Id] : Γ ⊩Id A)
       ([Π] : Γ ⊩Πirr B)
     → ShapeView Γ l l′ _ _ _ _ (Idᵣ [Id]) (Πirrᵣ [Π]) → ⊥
Id≢Π′ a b ()

Id≢Π-red : ∀ {B F G rF lF P t u Γ} → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
            → Γ ⊢ Id P t u ≡ B ^ [ % , ι ⁰ ] → ⊥
Id≢Π-red {ll} D = A≢B (λ Γ l A → Γ ⊩Id A)
                (λ Γ l A → Γ ⊩Πirr A) Idᵣ Πirrᵣ
                (λ x → extractMaybeEmb (Id-elim x))
                (λ x → extractMaybeEmb (Πirr-elim′ D x))
                Id≢Π′

-- U and Π F ▹ G for any F and G cannot be judgmentally equal.
Id≢Π! : ∀ {P t u F rF lF G Γ} → Γ ⊢ Id P t u ≡ Π F ^ rF ° lF ▹ G  ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ] → ⊥
Id≢Π! Id≡Π =
  let _ , ⊢Π = syntacticEq Id≡Π
  in Id≢Π-red (id ⊢Π) Id≡Π


U≢ne′ : ∀ {A lU r lK K Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ lU)
       ([K] : Γ ⊩ne K ^[ r , lK ] )
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {ll = lU} [U]) (ne [K]) → ⊥
U≢ne′ a b ()


U≢ne-red : ∀ {ll rU lU B K Γ} → Γ ⊢ B ⇒* K ^ [ ! , ι ll ] → Neutral K → Γ ⊢ Univ rU lU ≡ B ^ [ ! , ι ll ] → ⊥
U≢ne-red {ll} D neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ι ll) (λ Γ l B → Γ ⊩ne B ^[ ! , ll ]) Uᵣ ne
                     (λ x → extractMaybeEmb (U-elim x))
                     (λ x → extractMaybeEmb (ne-elim′ D neK x PE.refl))
                     U≢ne′

-- U and K for any neutral K cannot be judgmentally equal.
U≢ne! : ∀ {r l ll K Γ} → Neutral K → Γ ⊢ Univ r l ≡ K ^ [ ! , ι ll ] → ⊥
U≢ne! neK U≡K =
  let _ , ⊢K = syntacticEq U≡K
  in  U≢ne-red (id ⊢K) neK U≡K

ℕ≢Π′ : ∀ {A B Γ ll l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^[ ll ])
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (Πᵣ [Π]) → ⊥
ℕ≢Π′ a b ()


ℕ≢Π-red : ∀ {A B F rF lF lG G Γ} → Γ ⊢ A ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ ! ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ ⁰ ]) ℕᵣ Πᵣ
                   (λ x → extractMaybeEmb (ℕ-elim′ D x))
                   (λ x → extractMaybeEmb (Π-elim′ D′ x))
                   ℕ≢Π′

-- ℕ and Π F ▹ G for any F and G cannot be judgmentally equal.
ℕ≢Π! : ∀ {F rF G lF lG r Γ} → Γ ⊢ ℕ ≡ Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ r ^ [ ! , ι ⁰ ]  → ⊥
ℕ≢Π! ℕ≡Π =
  let ⊢ℕ , ⊢Π = syntacticEq ℕ≡Π
      rG , _ , _ , _ , _ , U=U , err , _ = inversion-Π (un-univ ⊢Π)
      r=r , _ = Univ-PE-injectivity (U≡A-whnf U=U Uₙ)
      eqr = PE.trans (PE.sym err) r=r
  in  ℕ≢Π-red (id ⊢ℕ) (id (PE.subst (λ X → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ^ [ _ , _ ] ) eqr ⊢Π)) (PE.subst (λ X → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ^ [ _ , _ ] ) eqr ℕ≡Π) 

-- Empty and Π
Empty≢Π′ : ∀ {A B Γ l l′}
       ([Empty] : Γ ⊩Empty A)
       ([Π] : Γ ⊩Πirr B)
     → ShapeView Γ l l′ _ _ _ _ (Emptyᵣ [Empty]) (Πirrᵣ [Π]) → ⊥
Empty≢Π′ a b ()

Empty≢Π-red : ∀ {A B F rF lF G Γ} → Γ ⊢ A ⇒* sEmpty ^ [ % , ι ⁰ ] → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
                → Γ ⊢ A ≡ B ^ [ % , ι ⁰ ] → ⊥
Empty≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩Empty A)
                   (λ Γ l A → Γ ⊩Πirr A) Emptyᵣ Πirrᵣ
                   (λ x → extractMaybeEmb (Empty-elim′ D x))
                   (λ x → extractMaybeEmb (Πirr-elim′ D′ x))
                   Empty≢Π′

Empty≢Π% : ∀ {F rF lF G Γ} → Γ ⊢ sEmpty ≡ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ] → ⊥
Empty≢Π% Empty≡Π =
  let ⊢Empty , ⊢Π = syntacticEq Empty≡Π
  in  Empty≢Π-red (id ⊢Empty) (id ⊢Π) Empty≡Π

ℕ≢ne′ : ∀ {ll A K Γ l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([K] : Γ ⊩ne K ^[ ! , ll ])
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (ne [K]) → ⊥
ℕ≢ne′ a b ()

ℕ≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* K ^ [ ! , ι ⁰ ] → Neutral K → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B ^[ ! , ⁰ ]) ℕᵣ ne
                        (λ x → extractMaybeEmb (ℕ-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl ))
                        ℕ≢ne′

-- ℕ and K for any neutral K cannot be judgmentally equal.
ℕ≢ne! : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ ≡ K ^ [ ! , ι ⁰ ] → ⊥
ℕ≢ne! neK ℕ≡K =
  let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
  in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

ℕ≢ℕ2′ : ∀ {A B Γ l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([ℕ2] : Γ ⊩ℕ2 B)
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (ℕ2ᵣ [ℕ2]) → ⊥
ℕ≢ℕ2′ a b ()

ℕ≢ℕ2-red : ∀ {A B Γ} → Γ ⊢ A ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* ℕ2 ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ≢ℕ2-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                   (λ Γ l A → Γ ⊩ℕ2 A) ℕᵣ ℕ2ᵣ
                   (λ x → extractMaybeEmb (ℕ-elim′ D x))
                   (λ x → extractMaybeEmb (ℕ2-elim′ D′ x))
                   ℕ≢ℕ2′

-- ℕ and ℕ2 cannot be judgmentally equal.
ℕ≢ℕ2! : ∀ {Γ} → Γ ⊢ ℕ ≡ ℕ2 ^ [ ! , ι ⁰ ] → ⊥
ℕ≢ℕ2! ℕ≡ℕ2 =
  let ⊢ℕ , ⊢ℕ2 = syntacticEq ℕ≡ℕ2
  in  ℕ≢ℕ2-red (id ⊢ℕ) (id ⊢ℕ2) ℕ≡ℕ2

ℕ2≢ℕ′ : ∀ {A B Γ l l′}
       ([ℕ2] : Γ ⊩ℕ2 A)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ _ _ (ℕ2ᵣ [ℕ2]) (ℕᵣ [ℕ]) → ⊥
ℕ2≢ℕ′ a b ()

ℕ2≢ℕ-red : ∀ {A B Γ} → Γ ⊢ A ⇒* ℕ2 ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ2≢ℕ-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ2 A)
                   (λ Γ l A → Γ ⊩ℕ A) ℕ2ᵣ ℕᵣ
                   (λ x → extractMaybeEmb (ℕ2-elim′ D x))
                   (λ x → extractMaybeEmb (ℕ-elim′ D′ x))
                   ℕ2≢ℕ′

ℕ2≢ℕ! : ∀ {Γ} → Γ ⊢ ℕ2 ≡ ℕ ^ [ ! , ι ⁰ ] → ⊥
ℕ2≢ℕ! ℕ2≡ℕ =
  let ⊢ℕ2 , ⊢ℕ = syntacticEq ℕ2≡ℕ
  in  ℕ2≢ℕ-red (id ⊢ℕ2) (id ⊢ℕ) ℕ2≡ℕ

U≢ℕ2′ : ∀ {Γ A ll B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ ll)
       ([ℕ2] : Γ ⊩ℕ2 B)
     → ShapeView Γ l l′ _ _ [ ! , _ ] [ ! , _ ] (Uᵣ {ll = ll} [U]) (ℕ2ᵣ [ℕ2]) → ⊥
U≢ℕ2′ a b ()

U≢ℕ2-red : ∀ {ll r lU B Γ} → Γ ⊢ B ⇒* ℕ2 ^ [ ! , ll ] → Γ ⊢ Univ r lU ≡ B ^ [ ! , ll ] → ⊥
U≢ℕ2-red {ll} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ll) (λ Γ l B → Γ ⊩ℕ2 B) Uᵣ ℕ2ᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ2-elim′ D x))
                U≢ℕ2′

U≢ℕ2! : ∀ {r l ll Γ} → Γ ⊢ Univ r l ≡ ℕ2 ^ [ ! , ll ] → ⊥
U≢ℕ2! U≡ℕ2 =
  let _ , ⊢ℕ2 = syntacticEq U≡ℕ2
  in  U≢ℕ2-red (id ⊢ℕ2) U≡ℕ2

ℕ2≢Π′ : ∀ {A B Γ ll l l′}
       ([ℕ2] : Γ ⊩ℕ2 A)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^[ ll ])
     → ShapeView Γ l l′ _ _ _ _ (ℕ2ᵣ [ℕ2]) (Πᵣ [Π]) → ⊥
ℕ2≢Π′ a b ()

ℕ2≢Π-red : ∀ {A B F rF lF lG G Γ} → Γ ⊢ A ⇒* ℕ2 ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ ! ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ2≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ2 A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ ⁰ ]) ℕ2ᵣ Πᵣ
                   (λ x → extractMaybeEmb (ℕ2-elim′ D x))
                   (λ x → extractMaybeEmb (Π-elim′ D′ x))
                   ℕ2≢Π′

ℕ2≢Π! : ∀ {F rF G lF lG r Γ} → Γ ⊢ ℕ2 ≡ Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ r ^ [ ! , ι ⁰ ]  → ⊥
ℕ2≢Π! ℕ2≡Π =
  let ⊢ℕ2 , ⊢Π = syntacticEq ℕ2≡Π
      rG , _ , _ , _ , _ , U=U , err , _ = inversion-Π (un-univ ⊢Π)
      r=r , _ = Univ-PE-injectivity (U≡A-whnf U=U Uₙ)
      eqr = PE.trans (PE.sym err) r=r
  in  ℕ2≢Π-red (id ⊢ℕ2) (id (PE.subst (λ X → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ^ [ _ , _ ] ) eqr ⊢Π)) (PE.subst (λ X → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ^ [ _ , _ ] ) eqr ℕ2≡Π)

ℕ2≢ne′ : ∀ {ll A K Γ l l′}
       ([ℕ2] : Γ ⊩ℕ2 A)
       ([K] : Γ ⊩ne K ^[ ! , ll ])
     → ShapeView Γ l l′ _ _ _ _ (ℕ2ᵣ [ℕ2]) (ne [K]) → ⊥
ℕ2≢ne′ a b ()

ℕ2≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* ℕ2 ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* K ^ [ ! , ι ⁰ ] → Neutral K → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ2≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ2 A) (λ Γ l B → Γ ⊩ne B ^[ ! , ⁰ ]) ℕ2ᵣ ne
                        (λ x → extractMaybeEmb (ℕ2-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl ))
                        ℕ2≢ne′

ℕ2≢ne! : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ2 ≡ K ^ [ ! , ι ⁰ ] → ⊥
ℕ2≢ne! neK ℕ2≡K =
  let ⊢ℕ2 , ⊢K = syntacticEq ℕ2≡K
  in  ℕ2≢ne-red (id ⊢ℕ2) (id ⊢K) neK ℕ2≡K

Ind≢ne′ : ∀ {ll A K Γ l l′ i}
       ([Ind] : Γ ⊩Ind A ^ i)
       ([K] : Γ ⊩ne K ^[ ! , ll ])
     → ShapeView Γ l l′ _ _ _ _ (Indᵣ [Ind]) (ne [K]) → ⊥
Ind≢ne′ a b ()

Ind≢ne-red : ∀ {A B K Γ i} → Γ ⊢ A ⇒* Ind i ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* K ^ [ ! , ι ⁰ ] → Neutral K → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
Ind≢ne-red {i = i} D D′ neK = A≢B (λ Γ l A → Γ ⊩Ind A ^ i)
                      (λ Γ l B → Γ ⊩ne B ^[ ! , ⁰ ]) Indᵣ ne
                      (λ x → extractMaybeEmb (Ind-elim′ D x))
                      (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl))
                      Ind≢ne′

-- Ind i and neutral K cannot be judgmentally equal.
Ind≢ne! : ∀ {i K Γ} → Neutral K → Γ ⊢ Ind i ≡ K ^ [ ! , ι ⁰ ] → ⊥
Ind≢ne! neK Ind≡K =
  let ⊢Ind , ⊢K = syntacticEq Ind≡K
  in  Ind≢ne-red (id ⊢Ind) (id ⊢K) neK Ind≡K

U≢Ind′ : ∀ {Γ A ll B i l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ ll)
       ([Ind] : Γ ⊩Ind B ^ i)
     → ShapeView Γ l l′ _ _ [ ! , _ ] [ ! , _ ] (Uᵣ {ll = ll} [U]) (Indᵣ [Ind]) → ⊥
U≢Ind′ a b ()

U≢Ind-red : ∀ {ll r lU i B Γ} → Γ ⊢ B ⇒* Ind i ^ [ ! , ll ] → Γ ⊢ Univ r lU ≡ B ^ [ ! , ll ] → ⊥
U≢Ind-red {ll} {i = i} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ll) (λ Γ l B → Γ ⊩Ind B ^ i) Uᵣ Indᵣ
                 (λ x → extractMaybeEmb (U-elim x))
                 (λ x → extractMaybeEmb (Ind-elim′ D x))
                 U≢Ind′

-- U and Ind i cannot be judgmentally equal.
U≢Ind! : ∀ {r l ll i Γ} → Γ ⊢ Univ r l ≡ Ind i ^ [ ! , ll ] → ⊥
U≢Ind! U≡Ind =
  let _ , ⊢Ind = syntacticEq U≡Ind
  in  U≢Ind-red (id ⊢Ind) U≡Ind

ℕ≢Ind′ : ∀ {A B Γ l l′ i}
       ([ℕ] : Γ ⊩ℕ A)
       ([Ind] : Γ ⊩Ind B ^ i)
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (Indᵣ [Ind]) → ⊥
ℕ≢Ind′ a b ()

ℕ≢Ind-red : ∀ {A B Γ i} → Γ ⊢ A ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* Ind i ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ≢Ind-red {i = i} D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                  (λ Γ l A → Γ ⊩Ind A ^ i) ℕᵣ Indᵣ
                  (λ x → extractMaybeEmb (ℕ-elim′ D x))
                  (λ x → extractMaybeEmb (Ind-elim′ D′ x))
                  ℕ≢Ind′

-- ℕ and Ind i cannot be judgmentally equal.
ℕ≢Ind! : ∀ {i Γ} → Γ ⊢ ℕ ≡ Ind i ^ [ ! , ι ⁰ ] → ⊥
ℕ≢Ind! ℕ≡Ind =
  let ⊢ℕ , ⊢Ind = syntacticEq ℕ≡Ind
  in  ℕ≢Ind-red (id ⊢ℕ) (id ⊢Ind) ℕ≡Ind

Ind≢ℕ′ : ∀ {A B Γ l l′ i}
       ([Ind] : Γ ⊩Ind A ^ i)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ _ _ (Indᵣ [Ind]) (ℕᵣ [ℕ]) → ⊥
Ind≢ℕ′ a b ()

Ind≢ℕ-red : ∀ {A B Γ i} → Γ ⊢ A ⇒* Ind i ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
Ind≢ℕ-red {i = i} D D′ = A≢B (λ Γ l A → Γ ⊩Ind A ^ i)
                  (λ Γ l A → Γ ⊩ℕ A) Indᵣ ℕᵣ
                  (λ x → extractMaybeEmb (Ind-elim′ D x))
                  (λ x → extractMaybeEmb (ℕ-elim′ D′ x))
                  Ind≢ℕ′

-- Ind i and ℕ cannot be judgmentally equal.
Ind≢ℕ! : ∀ {i Γ} → Γ ⊢ Ind i ≡ ℕ ^ [ ! , ι ⁰ ] → ⊥
Ind≢ℕ! Ind≡ℕ =
  let ⊢Ind , ⊢ℕ = syntacticEq Ind≡ℕ
  in  Ind≢ℕ-red (id ⊢Ind) (id ⊢ℕ) Ind≡ℕ

ℕ2≢Ind′ : ∀ {A B Γ l l′ i}
       ([ℕ2] : Γ ⊩ℕ2 A)
       ([Ind] : Γ ⊩Ind B ^ i)
     → ShapeView Γ l l′ _ _ _ _ (ℕ2ᵣ [ℕ2]) (Indᵣ [Ind]) → ⊥
ℕ2≢Ind′ a b ()

ℕ2≢Ind-red : ∀ {A B Γ i} → Γ ⊢ A ⇒* ℕ2 ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* Ind i ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ2≢Ind-red {i = i} D D′ = A≢B (λ Γ l A → Γ ⊩ℕ2 A)
                   (λ Γ l A → Γ ⊩Ind A ^ i) ℕ2ᵣ Indᵣ
                   (λ x → extractMaybeEmb (ℕ2-elim′ D x))
                   (λ x → extractMaybeEmb (Ind-elim′ D′ x))
                   ℕ2≢Ind′

-- ℕ2 and Ind i cannot be judgmentally equal.
ℕ2≢Ind! : ∀ {i Γ} → Γ ⊢ ℕ2 ≡ Ind i ^ [ ! , ι ⁰ ] → ⊥
ℕ2≢Ind! ℕ2≡Ind =
  let ⊢ℕ2 , ⊢Ind = syntacticEq ℕ2≡Ind
  in  ℕ2≢Ind-red (id ⊢ℕ2) (id ⊢Ind) ℕ2≡Ind

Ind≢ℕ2′ : ∀ {A B Γ l l′ i}
       ([Ind] : Γ ⊩Ind A ^ i)
       ([ℕ2] : Γ ⊩ℕ2 B)
     → ShapeView Γ l l′ _ _ _ _ (Indᵣ [Ind]) (ℕ2ᵣ [ℕ2]) → ⊥
Ind≢ℕ2′ a b ()

Ind≢ℕ2-red : ∀ {A B Γ i} → Γ ⊢ A ⇒* Ind i ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* ℕ2 ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
Ind≢ℕ2-red {i = i} D D′ = A≢B (λ Γ l A → Γ ⊩Ind A ^ i)
                   (λ Γ l A → Γ ⊩ℕ2 A) Indᵣ ℕ2ᵣ
                   (λ x → extractMaybeEmb (Ind-elim′ D x))
                   (λ x → extractMaybeEmb (ℕ2-elim′ D′ x))
                   Ind≢ℕ2′

-- Ind i and ℕ2 cannot be judgmentally equal.
Ind≢ℕ2! : ∀ {i Γ} → Γ ⊢ Ind i ≡ ℕ2 ^ [ ! , ι ⁰ ] → ⊥
Ind≢ℕ2! Ind≡ℕ2 =
  let ⊢Ind , ⊢ℕ2 = syntacticEq Ind≡ℕ2
  in  Ind≢ℕ2-red (id ⊢Ind) (id ⊢ℕ2) Ind≡ℕ2

Ind≢Π′ : ∀ {A B Γ ll l l′ i}
       ([Ind] : Γ ⊩Ind A ^ i)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^[ ll ])
     → ShapeView Γ l l′ _ _ _ _ (Indᵣ [Ind]) (Πᵣ [Π]) → ⊥
Ind≢Π′ a b ()

Ind≢Π-red : ∀ {A B F rF lF lG G Γ i} → Γ ⊢ A ⇒* Ind i ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ ! ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
Ind≢Π-red {i = i} D D′ = A≢B (λ Γ l A → Γ ⊩Ind A ^ i)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ ⁰ ]) Indᵣ Πᵣ
                   (λ x → extractMaybeEmb (Ind-elim′ D x))
                   (λ x → extractMaybeEmb (Π-elim′ D′ x))
                   Ind≢Π′

-- Ind i and Π F ▹ G for any F and G cannot be judgmentally equal.
Ind≢Π! : ∀ {i F rF G lF lG r Γ} → Γ ⊢ Ind i ≡ Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ r ^ [ ! , ι ⁰ ]  → ⊥
Ind≢Π! Ind≡Π =
  let ⊢Ind , ⊢Π = syntacticEq Ind≡Π
      rG , _ , _ , _ , _ , U=U , err , _ = inversion-Π (un-univ ⊢Π)
      r=r , _ = Univ-PE-injectivity (U≡A-whnf U=U Uₙ)
      eqr = PE.trans (PE.sym err) r=r
  in  Ind≢Π-red (id ⊢Ind) (id (PE.subst (λ X → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ^ [ _ , _ ] ) eqr ⊢Π)) (PE.subst (λ X → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ^ [ _ , _ ] ) eqr Ind≡Π)

Π≢Ind′ : ∀ {A B Γ ll l l′ i}
       ([Π] : Γ ⊩′⟨ l ⟩Π A ^[ ll ])
       ([Ind] : Γ ⊩Ind B ^ i)
     → ShapeView Γ l l′ _ _ _ _ (Πᵣ [Π]) (Indᵣ [Ind]) → ⊥
Π≢Ind′ a b ()

Π≢Ind-red : ∀ {A B F rF lF lG G lΠ Γ i} → Γ ⊢ A ⇒* Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ] → Γ ⊢ B ⇒* Ind i ^ [ ! , ι lΠ ] → Γ ⊢ A ≡ B ^ [ ! , ι lΠ ] → ⊥
Π≢Ind-red {lΠ = lΠ} {i = i} D D′ = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ lΠ ])
                   (λ Γ l B → Γ ⊩Ind B ^ i) Πᵣ Indᵣ
                   (λ x → extractMaybeEmb (Π-elim′ D x))
                   (λ x → extractMaybeEmb (Ind-elim′ D′ x))
                   Π≢Ind′

-- Π F ▹ G and Ind i for any F and G cannot be judgmentally equal.
Π≢Ind! : ∀ {F rF lF lG G l Γ i} → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ≡ Ind i ^ [ ! , ι l ] → ⊥
Π≢Ind! Π≡Ind =
  let ⊢Π , ⊢Ind = syntacticEq Π≡Ind
  in  Π≢Ind-red (id ⊢Π) (id ⊢Ind) Π≡Ind



-- Empty and neutral
Empty≢ne′ : ∀ {A K Γ l l′}
       ([Empty] : Γ ⊩Empty A )
       ([K] : Γ ⊩ne K ^[ % , ⁰ ])
     → ShapeView Γ l l′ _ _ _ _ (Emptyᵣ [Empty]) (ne [K]) → ⊥
Empty≢ne′ a b ()


Empty≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* sEmpty ^ [ % , ι ⁰ ] → Γ ⊢ B ⇒* K ^ [ % , ι ⁰ ] →
                                Neutral K → Γ ⊢ A ≡ B ^ [ % , ι ⁰ ] → ⊥
Empty≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩ne B ^[ % , ⁰ ]) Emptyᵣ ne
                        (λ x → extractMaybeEmb (Empty-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl))
                        Empty≢ne′

Empty≢ne% : ∀ {K Γ} → Neutral K → Γ ⊢ sEmpty ≡ K ^ [ % , ι ⁰ ]  → ⊥
Empty≢ne% neK Empty≡K =
  let ⊢Empty , ⊢K = syntacticEq Empty≡K
  in  Empty≢ne-red (id ⊢Empty) (id ⊢K) neK Empty≡K

Π≢ne′ : ∀ {ll A K Γ l l′}
       ([Π] : Γ ⊩′⟨ l ⟩Π A ^[  ll ])
       ([K] : Γ ⊩ne K ^[ ! , ll ])
     → ShapeView Γ l l′ _ _ _ _ (Πᵣ [Π]) (ne [K]) → ⊥
Π≢ne′ a b ()

Π≢ne-red : ∀ {ll A B F rF lF lG G K Γ} → Γ ⊢ A ⇒* Π F ^ rF ° lF ▹ G ° lG ° ll ^ ! ^ [ ! , ι ll ]
                                         → Γ ⊢ B ⇒* K ^ [ ! , ι ll ] → Neutral K
                                         → Γ ⊢ A ≡ B ^ [ ! , ι ll ] → ⊥
Π≢ne-red {ll} {r} D D′ neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ ll ])
                        (λ Γ l B → Γ ⊩ne B ^[ ! , ll ]) Πᵣ ne
                        (λ x → extractMaybeEmb (Π-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl))
                        Π≢ne′

-- Π F ▹ G and K for any F and G and neutral K cannot be judgmentally equal.
Π≢ne : ∀ {F rF lF lG r G K l Γ} → Neutral K → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ≡ K ^ [ ! , ι l ] → ⊥
Π≢ne neK Π≡K =
  let ⊢Π , ⊢K = syntacticEq Π≡K
      rG , _ , _ , _ , _ , U=U , err , _ = inversion-Π (un-univ ⊢Π)
      r=r , _ = Univ-PE-injectivity (U≡A-whnf U=U Uₙ)
      eqr = PE.trans (PE.sym err) r=r
  in  Π≢ne-red (id (PE.subst (λ X → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ^ [ _ , _ ] ) eqr ⊢Π)) (id ⊢K) neK (PE.subst (λ X → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ≡ _ ^ [ _ , _ ] ) eqr Π≡K)
