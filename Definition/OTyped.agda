module Definition.OTyped where
open import Definition.OUntyped
open import Tools.Nat using (Nat; 1+; _+_; _-_; plusZero; plusSuc; plus-comm; _<<_; _≟_; leS; le0; le-refl; le-plus-left; minus-suc)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary using (yes; no)
open import Tools.List using (List; map; foldr; length; range; length-map; range-suc; zip; _∷ʳ_; replicate; replicate-snoc; length-replicate; zip-range-cons; _∈ₗ_; hereₗ; thereₗ; ∈ₗ-map-1+; ∈ₗ-range; ∈ₗ-map-inv; zip-∈ₗ)
open import Tools.Inequality using (Bool; true; false; eqb; filter; filter-map; if_then_else_; filter-∈ₗ)
import Tools.List as TL
import Tools.PropositionalEquality as PE
open import Definition.Sort
import Definition.SUntyped as SU
import Definition.STyped as ST

infixl 30 _∙_
infix 30 Πⱼ_▹_▹_▹_

-- Well-typed variables
data _∷_^_∈_ : (x : Nat) (A : Term) (r : TypeInfo) (Γ : Con Term) → Set where
  here  : ∀ {Γ A r}                     →         0 ∷ wk1 A ^ r ∈ (Γ ∙ A ^ r )
  there : ∀ {Γ A rA B rB x} (h : x ∷ A ^ rA ∈ Γ) → Nat.suc x ∷ wk1 A ^ rA ∈ (Γ ∙ B ^ rB)

mutual
  -- Well-formed context
  data ⊢_ : Con Term → Set where
    ε   : ⊢ ε
    _∙_ : ∀ {Γ A r}
        → ⊢ Γ
        → Γ ⊢ A ^ r
        → ⊢ Γ ∙ A ^ r

  -- Well-formed type
  data _⊢_^_ (Γ : Con Term) : Term → TypeInfo → Set where
    Uⱼ    : ∀ {r} → ⊢ Γ → Γ ⊢ Univ r ¹ ^ [ ! , ∞ ]
    univ : ∀ {A r l}
         → Γ ⊢ A ∷ Univ r l ^ [ ! , next l ]
         → Γ ⊢ A ^ [ r , ι l ]

  -- Well-formed term of a type
  data _⊢_∷_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ : ∀ {r l l'}
         → l < l'
         → ⊢ Γ
         → Γ ⊢ (Univ r l) ∷ (Univ ! l') ^ [ ! , next l' ]
    ℕⱼ      : ⊢ Γ → Γ ⊢ ℕ ∷ U ⁰ ^ [ ! , ι ¹ ]
    ℕ2ⱼ     : ⊢ Γ → Γ ⊢ ℕ2 ∷ U ⁰ ^ [ ! , ι ¹ ]
    Emptyⱼ : ⊢ Γ → Γ ⊢ sEmpty ∷ SProp ^ [ ! , ι ¹ ]
    Πⱼ_▹_▹_▹_ : ∀ {F rF lF G lG r l}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ     ⊢ F ∷ (Univ rF lF) ^ [ ! , next lF ]
           → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ∷ (Univ r lG) ^ [ ! , next lG ]
           → Γ     ⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ∷ (Univ r l) ^ [ ! , next l ]
    var    : ∀ {A rl x}
           → ⊢ Γ
           → x ∷ A ^ rl ∈ Γ
           → Γ ⊢ var x ∷ A ^ rl
    lamⱼ    : ∀ {F r l rF lF G lG t}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ     ⊢ F ^ [ rF , ι lF ]
           → Γ ∙ F ^ [ rF , ι lF ] ⊢ t ∷ G ^ [ r , ι lG ]
           → Γ     ⊢ lam F ▹ t ^ l ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ^ [ r , ι l ]
    _▹_▹_▹_∘ⱼ_    : ∀ {g a F rF lF G lG r lΠ}
           → (r PE.≡ % → lG PE.≡ ⁰ × lΠ PE.≡ ⁰)
           → Γ     ⊢ F ∷ (Univ rF lF) ^ [ ! , next lF ]
           → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ∷ (Univ r lG) ^ [ ! , next lG ]
           → Γ ⊢     g ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r ^ [ r , ι lΠ ]
           → Γ ⊢     a ∷ F ^ [ rF , ι lF ]
           → Γ ⊢ g ∘ a ^ lΠ ∷ G [ a ] ^ [ r , ι lG ]
    fstⱼ : ∀ {A A' rA B B' e}
           → Γ ⊢ A ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
           → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ A' ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
           → Γ ∙ A' ^ [ rA , ι ⁰ ] ⊢ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ]
           → Γ ⊢ fst e ∷ Id (Univ rA ⁰) A A' ^ [ % , ι ⁰ ]
    sndⱼ : ∀ {A A' rA B B' e}
           → Γ ⊢ A ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
           → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ A' ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
           → Γ ∙ A' ^ [ rA , ι ⁰ ] ⊢ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ]
           → Γ ⊢ snd e ∷ Π A' ^ rA ° ⁰ ▹ Id (U ⁰)
                        (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                        B' ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
    zeroⱼ   : ⊢ Γ
           → Γ ⊢ zero ∷ ℕ ^ [ ! ,  ι ⁰ ]
    sucⱼ    : ∀ {n}
           → Γ ⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ ⊢ suc n ∷ ℕ ^ [ ! ,  ι ⁰ ]
    zero2ⱼ  : ⊢ Γ
           → Γ ⊢ zero2 ∷ ℕ2 ^ [ ! , ι ⁰ ]
    suc2ⱼ   : ∀ {n}
           → Γ ⊢ n ∷ ℕ2 ^ [ ! , ι ⁰ ]
           → Γ ⊢ suc2 n ∷ ℕ2 ^ [ ! , ι ⁰ ]
    natrecⱼ : ∀ {G rG lG s z n}
           → (rG PE.≡ % → lG PE.≡ ⁰)
           → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ G ^ [ rG , ι lG ]
           → Γ       ⊢ z ∷ G [ zero ] ^ [ rG , ι lG ]
           → Γ       ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (G ^ rG ° lG ▹▹ G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ [ rG , ι lG ]
           → Γ       ⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ       ⊢ natrec lG G z s n ∷ G [ n ] ^ [ rG , ι lG ]
    natrec2ⱼ : ∀ {G rG lG s z n}
           → (rG PE.≡ % → lG PE.≡ ⁰)
           → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ G ^ [ rG , ι lG ]
           → Γ       ⊢ z ∷ G [ zero2 ] ^ [ rG , ι lG ]
           → Γ       ⊢ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (G ^ rG ° lG ▹▹ G [ suc2 (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ [ rG , ι lG ]
           → Γ       ⊢ n ∷ ℕ2 ^ [ ! , ι ⁰ ]
           → Γ       ⊢ natrec2 lG G z s n ∷ G [ n ] ^ [ rG , ι lG ]
    Indⱼ    : ∀ {n} → ⊢ Γ → Γ ⊢ Ind n ∷ U ⁰ ^ [ ! , ι ¹ ]
    Ctrⱼ    : ∀ {i j args}
           → ⊢ Γ
           → Γ ⊢All args ∷ map emb-stype-oterm (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
           → Γ ⊢ ctr i j args ∷ Ind i ^ [ ! , ι ⁰ ]
    IndRectⱼ : ∀ {i P rG lG t ms}
           → (rG PE.≡ % → lG PE.≡ ⁰)
           → Γ ⊢ P ∷ Π Ind i ^ ! ° ⁰ ▹ Univ rG lG ° ¹ ° ¹ ^ ! ^ [ ! , ι ¹ ]
           → Γ ⊢ t ∷ Ind i ^ [ ! , ι ⁰ ]
           → Γ ⊢All ms ∷ indRectBranchTyList i P rG lG ^ [ rG , ι lG ]
           → Γ ⊢ IndRect i lG P t ms ∷ (P ∘ t ^ ¹) ^ [ rG , ι lG ]
    Emptyrecⱼ : ∀ {A lA rA e}
           → Γ ⊢ A ^ [ rA , ι lA ] → Γ ⊢ e ∷ sEmpty ^ [ % ,  ι ⁰ ] -> Γ ⊢ Emptyrec lA ⁰ A e ∷ A ^ [ rA , ι lA ]
    Idⱼ : ∀ {A l t u}
          → Γ ⊢ A ∷ U l ^ [ ! , next l ]
          → Γ ⊢ t ∷ A ^ [ ! , ι l ]
          → Γ ⊢ u ∷ A ^ [ ! , ι l ]
          → Γ ⊢ Id A t u ∷ SProp ^ [ ! , next ⁰ ]
    Idreflⱼ : ∀ {A l t}
              → Γ ⊢ t ∷ A ^ [ ! , ι l ]
              → Γ ⊢ Idrefl A t ∷ (Id A t t) ^ [ % , ι ⁰ ]
    transpⱼ : ∀ {A l P t s u e}
              → Γ ⊢ A ^ [ ! , l ]
              → Γ ∙ A ^ [ ! , l ] ⊢ P ^ [ % , ι ⁰ ]
              → Γ ⊢ t ∷ A ^ [ ! , l ]
              → Γ ⊢ s ∷ P [ t ] ^ [ % , ι ⁰ ]
              → Γ ⊢ u ∷ A ^ [ ! , l ]
              → Γ ⊢ e ∷ (Id A t u) ^ [ % , ι ⁰ ]
              → Γ ⊢ transp A P t s u e ∷ P [ u ] ^ [ % , ι ⁰ ]
    castⱼ : ∀ {A B r e t}
            → Γ ⊢ A ∷ Univ r ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ B ∷ Univ r ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ e ∷ (Id (Univ r ⁰) A B) ^ [ % , ι ⁰ ]
            → Γ ⊢ t ∷ A ^ [ r , ι ⁰ ]
            → Γ ⊢ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ]
    conv   : ∀ {t A B r}
           → Γ ⊢ t ∷ A ^ r
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ t ∷ B ^ r

  -- Well-typed lists of terms
  data _⊢All_∷_^_ (Γ : Con Term) : List Term → List Term → TypeInfo → Set where
    εⱼ   : ∀ {r} → Γ ⊢All TL.[] ∷ TL.[] ^ r
    consⱼ  : ∀ {t ts A As r}
         → Γ ⊢ t ∷ A ^ r
         → Γ ⊢All ts ∷ As ^ r
         → Γ ⊢All (t TL.∷ ts) ∷ (A TL.∷ As) ^ r

  -- Type equality
  data _⊢_≡_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ   : ∀ {A B r l}
           → Γ ⊢ A ≡ B ∷ (Univ r l) ^ [ ! , next l ]
           → Γ ⊢ A ≡ B ^ [ r , ι l ]
    refl   : ∀ {A r}
           → Γ ⊢ A ^ r
           → Γ ⊢ A ≡ A ^ r
    sym    : ∀ {A B r}
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ B ≡ A ^ r
    trans  : ∀ {A B C r}
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ B ≡ C ^ r
           → Γ ⊢ A ≡ C ^ r


  -- Term equality
  data _⊢_≡_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeInfo → Set where
    refl        : ∀ {t A l}
                → Γ ⊢ t ∷ A ^ [ ! , l ]
                → Γ ⊢ t ≡ t ∷ A ^ [ ! , l ]
    sym         : ∀ {t u A l}
                → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢ u ≡ t ∷ A ^ [ ! , l ]
    trans       : ∀ {t u v A l}
                → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢ u ≡ v ∷ A ^ [ ! , l ]
                → Γ ⊢ t ≡ v ∷ A ^ [ ! , l ]
    conv        : ∀ {A B r t u}
                → Γ ⊢ t ≡ u ∷ A ^ r
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t ≡ u ∷ B ^ r
    Π-cong      : ∀ {E F G H rF lF rG lG l}
                → (rG PE.≡ ! → lF ≤ l × lG ≤ l)
                → (rG PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
                → Γ     ⊢ F ^ [ rF , ι lF ]
                → Γ     ⊢ F ≡ H       ∷ (Univ rF lF) ^ [ ! , next lF ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≡ E       ∷ (Univ rG lG) ^ [ ! , next lG ]
                → Γ     ⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ rG ≡ Π H ^ rF ° lF ▹ E ° lG ° l ^ rG ∷ (Univ rG l) ^ [ ! , next l ]
    app-cong    : ∀ {a b f g F G rF lF lG l}
                → Γ ⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ ⊢ a ≡ b ∷ F ^ [ rF , ι lF ]
                → Γ ⊢ f ∘ a ^ l ≡ g ∘ b ^ l ∷ G [ a ] ^ [ ! , ι lG ]
    β-red       : ∀ {a t F rF lF G lG l}
                → lF ≤ l
                → lG ≤ l
                → Γ     ⊢ F ^ [ rF , ι lF ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢ t ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢ a ∷ F ^ [ rF , ι lF ]
                → Γ     ⊢ (lam F ▹ t ^ l) ∘ a ^ l ≡ t [ a ] ∷ G [ a ] ^ [ ! , ι lG ]
    η-eq        : ∀ {f g F rF lF lG l G}
                → lF ≤ l
                → lG ≤ l
                → Γ     ⊢ F ^ [ rF , ι lF ]
                → Γ     ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢ wk1 f ∘ var Nat.zero ^ l ≡ wk1 g ∘ var Nat.zero ^ l ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ ⊢ suc m ≡ suc n ∷ ℕ ^ [ ! ,  ι ⁰ ]
    suc2-cong   : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ2 ^ [ ! , ι ⁰ ]
                → Γ ⊢ suc2 m ≡ suc2 n ∷ ℕ2 ^ [ ! , ι ⁰ ]
    natrec-cong : ∀ {z z′ s s′ n n′ F F′ l}
                → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ F ≡ F′ ^ [ ! , ι l ]
                → Γ     ⊢ z ≡ z′ ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢ s ≡ s′ ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l  ]
                → Γ     ⊢ n ≡ n′ ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ     ⊢ natrec l F z s n ≡ natrec l F′ z′ s′ n′ ∷ F [ n ] ^ [ ! , ι l ]
    natrec2-cong : ∀ {z z′ s s′ n n′ F F′ l}
                → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ F ≡ F′ ^ [ ! , ι l ]
                → Γ     ⊢ z ≡ z′ ∷ F [ zero2 ] ^ [ ! , ι l ]
                → Γ     ⊢ s ≡ s′ ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc2 (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢ n ≡ n′ ∷ ℕ2 ^ [ ! , ι ⁰ ]
                → Γ     ⊢ natrec2 l F z s n ≡ natrec2 l F′ z′ s′ n′ ∷ F [ n ] ^ [ ! , ι l ]
    natrec-zero : ∀ {z s F l}
                → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢ natrec l F z s zero ≡ z ∷ F [ zero ] ^ [ ! , ι l ]
    natrec-suc  : ∀ {n z s F l}
                → Γ     ⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢ natrec l F z s (suc n) ≡ (s ∘ n ^ l) ∘ (natrec l F z s n) ^ l
                        ∷ F [ suc n ] ^ [ ! , ι l ]
    natrec2-zero : ∀ {z s F l}
                → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                → Γ     ⊢ z ∷ F [ zero2 ] ^ [ ! , ι l ]
                → Γ     ⊢ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc2 (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢ natrec2 l F z s zero2 ≡ z ∷ F [ zero2 ] ^ [ ! , ι l ]
    natrec2-suc  : ∀ {n z s F l}
                → Γ     ⊢ n ∷ ℕ2 ^ [ ! , ι ⁰ ]
                → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                → Γ     ⊢ z ∷ F [ zero2 ] ^ [ ! , ι l ]
                → Γ     ⊢ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc2 (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢ natrec2 l F z s (suc2 n) ≡ (s ∘ n ^ l) ∘ (natrec2 l F z s n) ^ l
                        ∷ F [ suc2 n ] ^ [ ! , ι l ]
    Emptyrec-cong : ∀ {A A' l e e'}
                → Γ ⊢ A ≡ A' ^ [ ! , ι l ]
                → Γ ⊢ e ∷ sEmpty ^ [ % , ι ⁰ ]
                → Γ ⊢ e' ∷ sEmpty ^ [ % , ι ⁰ ]
                → Γ ⊢ Emptyrec l ⁰  A e ≡ Emptyrec l ⁰  A' e' ∷ A ^ [ ! , ι l ]
    proof-irrelevance : ∀ {t u A l}
                      → Γ ⊢ t ∷ A ^ [ % , l ]
                      → Γ ⊢ u ∷ A ^ [ % , l ]
                      → Γ ⊢ t ≡ u ∷ A ^ [ % , l ]
    Id-cong : ∀ {A A' l t t' u u'}
              → Γ ⊢ A ≡ A' ∷ Univ ! l ^ [ ! , next l ]
              → Γ ⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
              → Γ ⊢ u ≡ u' ∷ A ^ [ ! , ι l ]
              → Γ ⊢ Id A t u ≡ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ]
    cast-refl : ∀ {A B e t} → let l = ⁰ in
                  Γ ⊢ A ≡ B ∷ U l ^ [ ! , next l ]
                → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
                → Γ ⊢ t ∷ A ^ [ ! , ι l ]
                → Γ ⊢ cast l A B e t ≡ t ∷ B ^ [ ! , ι l ]
    cast-cong : ∀ {A A' B B' e e' t t'} → let l = ⁰ in
                  Γ ⊢ A ≡ A' ∷ U l ^ [ ! , next l ]
                → Γ ⊢ B ≡ B' ∷ U l ^ [ ! , next l ]
                → Γ ⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
                → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
                → Γ ⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , ι ⁰ ]
                → Γ ⊢ cast l A B e t ≡ cast l A' B' e' t' ∷ B ^ [ ! , ι l ]
    cast-Π : ∀ {A A' rA B B' e f} → let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
               Γ ⊢ A ∷ (Univ rA lA) ^ [ ! , next lA ]
             → Γ ∙ A ^ [ rA , ι lA ] ⊢ B ∷ U lB ^ [ ! , next lB ]
             → Γ ⊢ A' ∷ (Univ rA lA) ^ [ ! , next lA ]
             → Γ ∙ A' ^ [ rA , ι lA ] ⊢ B' ∷ U lB ^ [ ! , next lB ]
             → Γ ⊢ e ∷ Id (U l) (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) ^ [ % , ι l ]
             → Γ ⊢ f ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) ^ [ ! , ι l ]
             → Γ ⊢ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f)
               ≡ (lam A' ▹
                      (let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                      cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ l))
                      ^ l)
                   ∷ Π A' ^ rA ° lA ▹ B' ° lB ° l  ^ ! ^ [ ! , ι l ]
    cast-ℕ-0 : ∀ {e}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e zero
                   ≡ zero
                   ∷ ℕ ^ [ ! , ι ⁰ ]
    cast-ℕ-S : ∀ {e n}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e (suc n)
                   ≡ suc (cast ⁰ ℕ ℕ e n)
                   ∷ ℕ ^ [ ! , ι ⁰ ]
    cast-ℕ2-0 : ∀ {e}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ2 ℕ2 ^ [ % , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ2 ℕ2 e zero2
                   ≡ zero2
                   ∷ ℕ2 ^ [ ! , ι ⁰ ]
    cast-ℕ2-S : ∀ {e n}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ2 ℕ2 ^ [ % , ι ⁰ ]
               → Γ ⊢ n ∷ ℕ2 ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ2 ℕ2 e (suc2 n)
                   ≡ suc2 (cast ⁰ ℕ2 ℕ2 e n)
                   ∷ ℕ2 ^ [ ! , ι ⁰ ]
    cast-Ind-ctr : ∀ {i j e args}
               → Γ ⊢ e ∷ Id (U ⁰) (Ind i) (Ind i) ^ [ % , ι ⁰ ]
               → Γ ⊢All args ∷ map emb-stype-oterm (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ (Ind i) (Ind i) e (ctr i j args)
                   ≡ ctr i j (map (λ a → cast ⁰ (Ind i) (Ind i) e a) args)
                   ∷ Ind i ^ [ ! , ι ⁰ ]

mutual
  data _⊢_⇒_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeLevel → Set where
    conv         : ∀ {A B l t u}
                 → Γ ⊢ t ⇒ u ∷ A ^ l
                 → Γ ⊢ A ≡ B ^ [ ! , l ]
                 → Γ ⊢ t ⇒ u ∷ B ^ l
    app-subst    : ∀ {A B t u a rA lA lB l}
                 → Γ     ⊢ A ∷ (Univ rA lA) ^ [ ! , next lA ]
                 → Γ ∙ A ^ [ rA , ι lA ] ⊢ B ∷ (U lB) ^ [ ! , next lB ]
                 → Γ ⊢ t ⇒ u ∷ Π A ^ rA ° lA ▹ B ° lB ° l ^ ! ^ ι l
                 → Γ ⊢ a ∷ A ^ [ rA , ι lA ]
                 → Γ ⊢ t ∘ a ^ l ⇒ u ∘ a ^ l  ∷ B [ a ] ^ ι lB
    β-red        : ∀ {A B lA lB a t rA l}
                 → lA ≤ l
                 → lB ≤ l
                 → Γ     ⊢ A ^ [ rA , ι lA ]
                 → Γ ∙ A ^ [ rA , ι lA ] ⊢ B ∷ (U lB) ^ [ ! , next lB ]
                 → Γ ∙ A ^ [ rA , ι lA ] ⊢ t ∷ B ^ [ ! , ι lB ]
                 → Γ     ⊢ a ∷ A ^ [ rA , ι lA ]
                 → Γ     ⊢ (lam A ▹ t ^ l) ∘ a ^ l ⇒ t [ a ] ∷ B [ a ] ^ ι lB
    natrec-subst : ∀ {z s n n′ F l}
                 → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                 → Γ     ⊢ n ⇒ n′ ∷ ℕ ^ ι ⁰
                 → Γ     ⊢ natrec l F z s n ⇒ natrec l F z s n′ ∷ F [ n ] ^ ι l
    natrec2-subst : ∀ {z s n n′ F l}
                 → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero2 ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc2 (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                 → Γ     ⊢ n ⇒ n′ ∷ ℕ2 ^ ι ⁰
                 → Γ     ⊢ natrec2 l F z s n ⇒ natrec2 l F z s n′ ∷ F [ n ] ^ ι l
    natrec-zero  : ∀ {z s F l }
                 → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                 → Γ     ⊢ natrec l F z s zero ⇒ z ∷ F [ zero ] ^ ι l
    natrec-suc   : ∀ {n z s F l}
                 → Γ     ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
                 → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                 → Γ     ⊢ natrec l F z s (suc n) ⇒ (s ∘ n ^ l) ∘ (natrec l F z s n) ^ l
                         ∷ F [ suc n ] ^ ι l
    natrec2-zero  : ∀ {z s F l}
                 → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero2 ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc2 (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                 → Γ     ⊢ natrec2 l F z s zero2 ⇒ z ∷ F [ zero2 ] ^ ι l
    natrec2-suc   : ∀ {n z s F l}
                 → Γ     ⊢ n ∷ ℕ2 ^ [ ! , ι ⁰ ]
                 → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero2 ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc2 (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                 → Γ     ⊢ natrec2 l F z s (suc2 n) ⇒ (s ∘ n ^ l) ∘ (natrec2 l F z s n) ^ l
                         ∷ F [ suc2 n ] ^ ι l
    cast-subst : ∀ {A A' B e t} → let l = ⁰ in
                    Γ ⊢ A ⇒ A' ∷ U l ^ next l
                  → Γ ⊢ B ∷ U l ^ [ ! , next l ]
                  → Γ ⊢ e ∷ Id (U l) A B ^ [ % , ι ⁰ ]
                  → Γ ⊢ t ∷ A ^ [ ! , ι l ]
                  → Γ ⊢ cast l A B e t ⇒ cast l A' B e t ∷ B ^ ι l
    cast-ne-subst : ∀ {K B B' e t} → let l = ⁰ in
                    Γ ⊢ K ∷ U l ^ [ ! , next l ]
                  → Neutral K
                  → Γ ⊢ B ⇒ B' ∷ U l ^ next l
                  → Γ ⊢ e ∷ Id (U l) K B ^ [ % , ι ⁰ ]
                  → Γ ⊢ t ∷ K ^ [ ! , ι l ]
                  → Γ ⊢ cast l K B e t ⇒ cast l K B' e t ∷ B ^ ι l
    cast-ℕ-subst : ∀ {B B' e t}
                  → Γ ⊢ B ⇒ B' ∷ U ⁰ ^ next ⁰
                  → Γ ⊢ e ∷ Id (U ⁰) ℕ B ^ [ % , ι ⁰ ]
                  → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
                  → Γ ⊢ cast ⁰ ℕ B e t ⇒ cast ⁰ ℕ B' e t ∷ B ^ ι ⁰
    cast-Π-subst : ∀ {A rA P B B' e t} → let l = ⁰ in let lA = ⁰ in let lP = ⁰ in
                    Γ ⊢ A ∷ (Univ rA lA) ^ [ ! , next lA ]
                  → Γ ∙ A ^ [ rA , ι lA ] ⊢ P ∷ U lP ^ [ ! , next lA ]
                  → Γ ⊢ B ⇒ B' ∷ U l ^ next l
                  → Γ ⊢ e ∷ Id (U l) (Π A ^ rA ° lA ▹ P ° lP ° l ^ !) B ^ [ % , ι l ]
                  → Γ ⊢ t ∷ (Π A ^ rA ° lA ▹ P ° lP ° l ^ !) ^ [ ! , ι l ]
                  → Γ ⊢ cast l (Π A ^ rA ° lA ▹ P ° lP ° l ^ !) B e t ⇒ cast l (Π A ^ rA ° lA ▹ P ° lP ° l ^ !) B' e t ∷ B ^ ι l
    cast-Π : ∀ {A A' rA B B' e f} → let l = ⁰ in
               Γ ⊢ A ∷ (Univ rA l) ^ [ ! , next l ]
             → Γ ∙ A ^ [ rA , ι l ] ⊢ B ∷ U l ^ [ ! , next l ]
             → Γ ⊢ A' ∷ (Univ rA l) ^ [ ! , next l ]
             → Γ ∙ A' ^ [ rA , ι l ] ⊢ B' ∷ U l ^ [ ! , next l ]
             → Γ ⊢ e ∷ Id (U l) (Π A ^ rA ° l ▹ B ° l ° l ^ !) (Π A' ^ rA ° l  ▹ B' ° l ° l ^ !) ^ [ % , ι l ]
             → Γ ⊢ f ∷ (Π A ^ rA ° l ▹ B ° l ° l ^ !) ^ [ ! , ι l ]
             → Γ ⊢ (cast l (Π A ^ rA ° l ▹ B ° l ° l ^ !) (Π A' ^ rA ° l ▹ B' ° l ° l ^ !) e f)
               ⇒ (lam A' ▹
                      (let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)
                       in cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ l))
                       ^ l )
                   ∷ Π A' ^ rA ° l ▹ B' ° l ° l ^ ! ^ ι l
    cast-ℕ-0 : ∀ {e}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e zero
                   ⇒ zero
                   ∷ ℕ ^ ι ⁰
    cast-ℕ-S : ∀ {e n}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e (suc n)
                   ⇒ suc (cast ⁰ ℕ ℕ e n)
                   ∷ ℕ ^ ι ⁰

    cast-ℕ-cong : ∀ {e t u}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢ t ⇒ u ∷ ℕ ^ ι ⁰
               → Γ ⊢ cast ⁰ ℕ ℕ e t
                   ⇒ cast ⁰ ℕ ℕ e u
                   ∷ ℕ ^ ι ⁰

    cast-ne-cong : ∀ {K L e t u} → 
                 Γ ⊢ K ∷ U ⁰ ^ [ ! , next ⁰ ]
               → Neutral K
               → Γ ⊢ L ∷ U ⁰ ^ [ ! , next ⁰ ]
               → Neutral L
               → Γ ⊢ e ∷ Id (U ⁰) K L ^ [ % , ι ⁰ ]
               → Γ ⊢ t ⇒ u ∷ K ^ ι ⁰
               → Γ ⊢ cast ⁰ K L e t
                   ⇒ cast ⁰ K L e u
                   ∷ L ^ ι ⁰

  -- Type reduction
  data _⊢_⇒_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ : ∀ {A B r l}
         → Γ ⊢ A ⇒ B ∷ (Univ r l) ^ next l
         → Γ ⊢ A ⇒ B ^ [ r , ι l ]

-- Term reduction closure
data _⊢_⇒*_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeLevel → Set where
  id  : ∀ {A l t}
      → Γ ⊢ t ∷ A ^ [ ! , l ]
      → Γ ⊢ t ⇒* t ∷ A ^ l
  _⇨_ : ∀ {A l t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A ^ l
      → Γ ⊢ t′ ⇒* u  ∷ A ^ l
      → Γ ⊢ t  ⇒* u  ∷ A ^ l

-- Type reduction closure
data _⊢_⇒*_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
  id  : ∀ {A r}
      → Γ ⊢ A ^ r
      → Γ ⊢ A ⇒* A ^ r
  _⇨_ : ∀ {A A′ B r}
      → Γ ⊢ A  ⇒  A′ ^ r
      → Γ ⊢ A′ ⇒* B  ^ r
      → Γ ⊢ A  ⇒* B  ^ r

-- Type reduction to whnf
_⊢_↘_^_ : (Γ : Con Term) → Term → Term → TypeInfo → Set
Γ ⊢ A ↘ B ^ r = Γ ⊢ A ⇒* B ^ r × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_^_ : (Γ : Con Term) → Term → Term → Term → TypeLevel → Set
Γ ⊢ t ↘ u ∷ A ^ l = Γ ⊢ t ⇒* u ∷ A ^ l × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_^_ : (Γ : Con Term) → Term → Term → TypeInfo → Set
Γ ⊢ A :≡: B ^ r = Γ ⊢ A ^ r × Γ ⊢ B ^ r × (Γ ⊢ A ≡ B ^ r)

-- Term equality with well-formed terms
_⊢_:≡:_∷_^_ : (Γ : Con Term) → Term → Term → Term → TypeInfo → Set
Γ ⊢ t :≡: u ∷ A ^ r = Γ ⊢ t ∷ A ^ r × Γ ⊢ u ∷ A ^ r × (Γ ⊢ t ≡ u ∷ A ^ r)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_^_ (Γ : Con Term) (A B : Term) (r : TypeInfo) : Set where
  constructor [[_,_,_]]
  field
    ⊢A : Γ ⊢ A ^ r
    ⊢B : Γ ⊢ B ^ r
    D  : Γ ⊢ A ⇒* B ^ r

open _⊢_:⇒*:_^_ using () renaming (D to red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_^_ (Γ : Con Term) (t u A : Term) (l : TypeLevel) : Set where
  constructor [[_,_,_]]
  field
    ⊢t : Γ ⊢ t ∷ A ^ [ ! , l ]
    ⊢u : Γ ⊢ u ∷ A ^ [ ! , l ]
    d  : Γ ⊢ t ⇒* u ∷ A ^ l

open _⊢_:⇒*:_∷_^_ using () renaming (d to redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con Term) (σ : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {Γ A rA}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢ head σ ∷ subst (tail σ) A ^ rA
      → Δ ⊢ˢ σ ∷ Γ ∙ A ^ rA

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con Term) (σ σ′ : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {Γ A rA}
      → Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢ head σ ≡ head σ′ ∷ subst (tail σ) A ^ rA
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ ∙ A ^ rA

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

-- Some derivable rules
Unitⱼ : ∀ {Γ} (⊢Γ : ⊢ Γ)
      → Γ ⊢ sUnit ∷ SProp ^ [ ! , next ⁰ ]
Unitⱼ ⊢Γ = Πⱼ (λ abs → ⊥-elim (!≢% (PE.sym abs))) ▹ (λ _ → PE.refl , PE.refl) ▹ Emptyⱼ ⊢Γ ▹ Emptyⱼ (⊢Γ ∙ univ (Emptyⱼ ⊢Γ))

Ugenⱼ : ∀ {r Γ l} → ⊢ Γ → Γ ⊢ Univ r l ^ [ ! , next l ]
Ugenⱼ {l = ⁰} ⊢Γ = univ (univ 0<1 ⊢Γ)
Ugenⱼ {l = ¹} ⊢Γ = Uⱼ ⊢Γ


-- embedding of simple terms into OTerm preserves typing

emb-scon : ST.Con → Con Term
emb-scon TL.[] = ε
emb-scon (A TL.∷ Γ) = emb-scon Γ ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ]

emb-sterm-oterm-preserves-typing : ∀ {Γ t A}
  → Γ ST.⊢ t ∷ A
  → emb-scon Γ ⊢ emb-sterm-oterm t ∷ emb-stype-oterm A ^ [ ! , ι ⁰ ]
emb-sterm-oterm-preserves-typing = go
  where
  Π⁰ : Term → Term → Term
  Π⁰ A B = Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !

  emb-stype-oterm-has-type : ∀ (A : SU.Type) {Γ} → ⊢ Γ → Γ ⊢ emb-stype-oterm A ∷ U ⁰ ^ [ ! , next ⁰ ]
  emb-stype-oterm-has-type (SU.Ind n) ⊢Γ = Indⱼ ⊢Γ
  emb-stype-oterm-has-type (SU.Arrow A B) ⊢Γ =
    Πⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) ▹ (λ ()) ▹ (emb-stype-oterm-has-type A ⊢Γ)
       ▹ (emb-stype-oterm-has-type B (⊢Γ ∙ univ (emb-stype-oterm-has-type A ⊢Γ)))

  emb-scon-wf : ∀ Γ → ⊢ (emb-scon Γ)
  emb-scon-wf TL.[] = ε
  emb-scon-wf (A TL.∷ Γ) = emb-scon-wf Γ ∙ univ (emb-stype-oterm-has-type A (emb-scon-wf Γ))

  mutual
    emb-stype-wk-id : ∀ A ρ → wk ρ (emb-stype-oterm A) PE.≡ emb-stype-oterm A
    emb-stype-wk-id (SU.Ind _) ρ = PE.refl
    emb-stype-wk-id (SU.Arrow A B) ρ =
      PE.cong (gen (Pikind ! ⁰ ⁰ ⁰ !)) (emb-stype-wkGen-id A B ρ)

    emb-stype-wkGen-id : ∀ A B ρ
      → wkGen ρ (⟦ 0 , emb-stype-oterm A ⟧ TL.∷ ⟦ 1 , emb-stype-oterm B ⟧ TL.∷ TL.[])
      PE.≡ (⟦ 0 , emb-stype-oterm A ⟧ TL.∷ ⟦ 1 , emb-stype-oterm B ⟧ TL.∷ TL.[])
    emb-stype-wkGen-id A B ρ =
      PE.cong₂ TL._∷_
        (PE.cong (λ t → ⟦ 0 , t ⟧) (emb-stype-wk-id A (repeat lift ρ 0)))
        (PE.cong₂ TL._∷_
          (PE.cong (λ t → ⟦ 1 , t ⟧) (emb-stype-wk-id B (repeat lift ρ 1)))
          PE.refl)

  emb-stype-wk1n-id : ∀ A n → repeat wk1 (emb-stype-oterm A) n PE.≡ emb-stype-oterm A
  emb-stype-wk1n-id A 0 = PE.refl
  emb-stype-wk1n-id A (1+ n) =
    PE.trans (PE.cong wk1 (emb-stype-wk1n-id A n)) (emb-stype-wk-id A (step id))

  emb-st-var-wk-depth : ∀ {x A Γ} → x ST.∷ A ∈ Γ → Nat
  emb-st-var-wk-depth ST.here = 1
  emb-st-var-wk-depth (ST.there h) = 1+ (emb-st-var-wk-depth h)

  emb-st-var∈ : ∀ {x A Γ} (h : x ST.∷ A ∈ Γ)
    → x ∷ repeat wk1 (emb-stype-oterm A) (emb-st-var-wk-depth h) ^ [ ! , ι ⁰ ] ∈ emb-scon Γ
  emb-st-var∈ ST.here = here
  emb-st-var∈ (ST.there h) = there (emb-st-var∈ h)

  emb-st-wkTy≡ : ∀ {Γ A} d → ⊢ (emb-scon Γ)
    → emb-scon Γ ⊢ repeat wk1 (emb-stype-oterm A) d ≡ emb-stype-oterm A ^ [ ! , ι ⁰ ]
  emb-st-wkTy≡ {Γ} {A} d ⊢Γ =
    PE.subst (λ (embTy : Term) → emb-scon Γ ⊢ repeat wk1 (emb-stype-oterm A) d ≡ embTy ^ [ ! , ι ⁰ ])
            (emb-stype-wk1n-id A d)
            (refl (PE.subst (λ (embTy : Term) → emb-scon Γ ⊢ embTy ^ [ ! , ι ⁰ ])
                           (PE.sym (emb-stype-wk1n-id A d))
                           (univ (emb-stype-oterm-has-type A ⊢Γ))))

  mutual
    emb-stype-subst-id : ∀ A σ → subst σ (emb-stype-oterm A) PE.≡ emb-stype-oterm A
    emb-stype-subst-id (SU.Ind _) σ = PE.refl
    emb-stype-subst-id (SU.Arrow A B) σ =
      PE.cong (gen (Pikind ! ⁰ ⁰ ⁰ !)) (emb-stype-substGen-id A B σ)

    emb-stype-substGen-id : ∀ A B σ
      → substGen σ (⟦ 0 , emb-stype-oterm A ⟧ TL.∷ ⟦ 1 , emb-stype-oterm B ⟧ TL.∷ TL.[])
      PE.≡ (⟦ 0 , emb-stype-oterm A ⟧ TL.∷ ⟦ 1 , emb-stype-oterm B ⟧ TL.∷ TL.[])
    emb-stype-substGen-id A B σ =
      PE.cong₂ TL._∷_
        (PE.cong (λ t → ⟦ 0 , t ⟧) (emb-stype-subst-id A (repeat liftSubst σ 0)))
        (PE.cong₂ TL._∷_
          (PE.cong (λ t → ⟦ 1 , t ⟧) (emb-stype-subst-id B (repeat liftSubst σ 1)))
          PE.refl)

  _∙∙_ : Con Term → List Term → Con Term
  Γ ∙∙ TL.[] = Γ
  Γ ∙∙ (A TL.∷ As) = (Γ ∙ A ^ [ ! , ι ⁰ ]) ∙∙ As

  ∙∙-∷ʳ : ∀ Γ As A → (Γ ∙∙ As) ∙ A ^ [ ! , ι ⁰ ] PE.≡ Γ ∙∙ (As TL.∷ʳ A)
  ∙∙-∷ʳ Γ TL.[] A = PE.refl
  ∙∙-∷ʳ Γ (B TL.∷ As) A = ∙∙-∷ʳ (Γ ∙ B ^ [ ! , ι ⁰ ]) As A

  repeat-wk1-comm : ∀ n t → repeat wk1 (wk1 t) n PE.≡ wk1 (repeat wk1 t n)
  repeat-wk1-comm 0 t = PE.refl
  repeat-wk1-comm (1+ n) t = PE.cong wk1 (repeat-wk1-comm n t)

  there* : ∀ {Γ x A r} As →
    x ∷ A ^ r ∈ Γ →
    (length As + x) ∷ repeat wk1 A (length As) ^ r ∈ (Γ ∙∙ As)
  there* TL.[] h = h
  there* {Γ} {x} {A} {r} (B TL.∷ As) h =
    PE.subst₂ (λ n ty → n ∷ ty ^ r ∈ ((Γ ∙ B ^ [ ! , ι ⁰ ]) ∙∙ As))
      (plusSuc (length As) x)
      (repeat-wk1-comm (length As) A)
      (there* As (there h))

  ⊢∙∙-stypes : ∀ {Γ} As → ⊢ Γ → ⊢ (Γ ∙∙ map emb-stype-oterm As)
  ⊢∙∙-stypes TL.[] ⊢Γ = ⊢Γ
  ⊢∙∙-stypes {Γ} (A TL.∷ As) ⊢Γ =
    ⊢∙∙-stypes {Γ = Γ ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ]} As
      (⊢Γ ∙ univ (emb-stype-oterm-has-type A ⊢Γ))

  wk1^-Pλ : ∀ n i P →
    wk1^ n (lam (Ind i) ▹ wk1 (emb-stype-oterm P) ^ ¹) PE.≡
    lam (Ind i) ▹ wk1 (emb-stype-oterm P) ^ ¹
  wk1^-Pλ 0 i P = PE.refl
  wk1^-Pλ (1+ n) i P =
    PE.trans (PE.cong wk1 (wk1^-Pλ n i P))
      (PE.cong (λ t → lam (Ind i) ▹ t ^ ¹)
        (PE.trans (PE.cong (wk (lift (step id))) (emb-stype-wk-id P (step id)))
          (PE.trans (emb-stype-wk-id P (lift (step id)))
            (PE.sym (emb-stype-wk-id P (step id))))))

  β-const-P : ∀ {Γ} i P a →
    ⊢ Γ →
    Γ ⊢ a ∷ Ind i ^ [ ! , ι ⁰ ] →
    Γ ⊢ (lam (Ind i) ▹ wk1 (emb-stype-oterm P) ^ ¹) ∘ a ^ ¹
        ≡ emb-stype-oterm P ∷ U ⁰ ^ [ ! , next ⁰ ]
  β-const-P {Γ} i P a ⊢Γ ⊢a =
    let ⊢Ind = univ (Indⱼ ⊢Γ)
        ⊢Pemb∙ = emb-stype-oterm-has-type P (⊢Γ ∙ ⊢Ind)
        ⊢wk1Pemb =
          PE.subst (λ u → Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ u ∷ U ⁰ ^ [ ! , next ⁰ ])
            (PE.sym (emb-stype-wk-id P (step id)))
            ⊢Pemb∙
        βeq = β-red (⁰min ¹) (≡is≤ PE.refl) ⊢Ind ⊢wk1Pemb ⊢a
    in  PE.subst
          (λ T → Γ ⊢ (lam (Ind i) ▹ wk1 (emb-stype-oterm P) ^ ¹) ∘ a ^ ¹
                    ≡ T ∷ U ⁰ ^ [ ! , next ⁰ ])
          (PE.trans (PE.cong (λ u → u [ a ]) (emb-stype-wk-id P (step id)))
            (emb-stype-subst-id P (sgSubst a)))
          βeq

  data TysEq (Γ : Con Term) : List Term → List Term → TypeInfo → Set where
    ε : ∀ {r} → TysEq Γ TL.[] TL.[] r
    cons : ∀ {A B As Bs r}
        → Γ ⊢ A ≡ B ^ r
        → TysEq Γ As Bs r
        → TysEq Γ (A TL.∷ As) (B TL.∷ Bs) r

  convAll : ∀ {Γ ts As Bs r}
    → Γ ⊢All ts ∷ As ^ r
    → TysEq Γ As Bs r
    → Γ ⊢All ts ∷ Bs ^ r
  convAll εⱼ ε = εⱼ
  convAll (consⱼ ⊢t ⊢ts) (cons A≡B As≡Bs) = consⱼ (conv ⊢t A≡B) (convAll ⊢ts As≡Bs)

  ⊢All-ctor-vars : ∀ {Γ} As k P →
    ⊢ ((Γ ∙∙ map emb-stype-oterm As) ∙∙ replicate k (emb-stype-oterm P)) →
    ((Γ ∙∙ map emb-stype-oterm As) ∙∙ replicate k (emb-stype-oterm P))
      ⊢All map (λ j → var (((k + length As) - 1) - j)) (range (length As))
          ∷ map emb-stype-oterm As ^ [ ! , ι ⁰ ]
  ⊢All-ctor-vars {Γ} TL.[] k P ⊢Γ' = εⱼ
  ⊢All-ctor-vars {Γ} (A TL.∷ As) k P ⊢Γ' =
    PE.subst
      (λ ts → ((Γ ∙∙ map emb-stype-oterm (A TL.∷ As)) ∙∙ Ihs)
                ⊢All ts ∷ (emb-stype-oterm A TL.∷ map emb-stype-oterm As) ^ [ ! , ι ⁰ ])
      (PE.sym (ctor-vars-cons k A As))
      (consⱼ
        (conv (var ⊢Γ' ∈A)
              (PE.subst (λ T → ((Γ ∙∙ map emb-stype-oterm (A TL.∷ As)) ∙∙ Ihs)
                                 ⊢ T ≡ emb-stype-oterm A ^ [ ! , ι ⁰ ])
                (PE.sym (emb-stype-wk1n-nested A (length (map emb-stype-oterm As)) k))
                (refl (univ (emb-stype-oterm-has-type A ⊢Γ')))))
        (⊢All-ctor-vars {Γ = Γ ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ]} As k P ⊢Γ'))
    where
    Ihs = replicate k (emb-stype-oterm P)
    emb-stype-wk1n-nested : ∀ A n m →
      repeat wk1 (repeat wk1 (wk1 (emb-stype-oterm A)) n) m PE.≡ emb-stype-oterm A
    emb-stype-wk1n-nested A n m =
      PE.trans
        (PE.cong (λ t → repeat wk1 t m)
          (PE.trans (PE.cong (λ t → repeat wk1 t n) (emb-stype-wk-id A (step id)))
            (emb-stype-wk1n-id A n)))
        (emb-stype-wk1n-id A m)
    ∈A : (k + length As) ∷ repeat wk1 (repeat wk1 (wk1 (emb-stype-oterm A))
           (length (map emb-stype-oterm As))) k ^ [ ! , ι ⁰ ]
           ∈ ((Γ ∙∙ map emb-stype-oterm (A TL.∷ As)) ∙∙ Ihs)
    ∈A = PE.subst (λ n → (k + n) ∷ repeat wk1 (repeat wk1 (wk1 (emb-stype-oterm A))
                           (length (map emb-stype-oterm As))) k ^ [ ! , ι ⁰ ]
                           ∈ ((Γ ∙∙ map emb-stype-oterm (A TL.∷ As)) ∙∙ Ihs))
           (length-map emb-stype-oterm As)
           (PE.subst (λ ℓ → (ℓ + length (map emb-stype-oterm As)) ∷
                              repeat wk1 (repeat wk1 (wk1 (emb-stype-oterm A))
                                (length (map emb-stype-oterm As))) ℓ ^ [ ! , ι ⁰ ]
                              ∈ ((Γ ∙∙ map emb-stype-oterm (A TL.∷ As)) ∙∙ Ihs))
             (length-replicate k (emb-stype-oterm P))
             (there* Ihs
               (PE.subst (λ n → n ∷ repeat wk1 (wk1 (emb-stype-oterm A))
                                    (length (map emb-stype-oterm As)) ^ _
                                  ∈ (_ ∙∙ map emb-stype-oterm As))
                 (plusZero (length (map emb-stype-oterm As)))
                 (there* (map emb-stype-oterm As) here))))
    ctor-vars-cons : ∀ {A} (k : Nat) (a : A) (as : List A) →
      map (λ j → var (((k + length (a TL.∷ as)) - 1) - j)) (range (length (a TL.∷ as)))
      PE.≡ var (k + length as) TL.∷
           map (λ j → var (((k + length as) - 1) - j)) (range (length as))
    ctor-vars-cons k a as =
      let n' = length as
          f : Nat → Term
          f j = var (((k + 1+ n') - 1) - j)
          g : Nat → Term
          g j = var ((k + n') - j)
          h : Nat → Term
          h j = var (((k + n') - 1) - j)
          sucₙ : Nat → Nat
          sucₙ n = 1+ n
          step₁ : map f (range (1+ n')) PE.≡ map g (range (1+ n'))
          step₁ = PE.cong (λ m → map (λ j → var ((m - 1) - j)) (range (1+ n')))
                    (plusSuc k n')
          step₂ : map g (range (1+ n')) PE.≡ g 0 TL.∷ map g (map sucₙ (range n'))
          step₂ = PE.cong (map g) (range-suc n')
          step₃ : map g (map sucₙ (range n')) PE.≡ map h (range n')
          step₃ = PE.trans (map-map g sucₙ (range n'))
                    (map-cong (range n') (λ j → PE.cong var (minus-suc (k + n') j)))
      in PE.trans step₁ (PE.trans step₂ (PE.cong (var (k + n') TL.∷_) step₃))

  ⊢-ctr : ∀ {Γ} i j k P →
    let as = SU.ctrArgsTypeList i j
        n = length (ctrArgsTypeList i j)
        Γ' = (Γ ∙∙ map emb-stype-oterm as) ∙∙ replicate k (emb-stype-oterm P)
    in ⊢ Γ' →
       Γ' ⊢ ctr i j (map (λ j → var (((k + n) - 1) - j)) (range n))
         ∷ Ind i ^ [ ! , ι ⁰ ]
  ⊢-ctr {Γ} i j k P ⊢Γ' =
    let as = SU.ctrArgsTypeList i j
        Γ' = (Γ ∙∙ map emb-stype-oterm as) ∙∙ replicate k (emb-stype-oterm P)
    in  Ctrⱼ ⊢Γ' (PE.subst
          (λ n → Γ' ⊢All map (λ j → var (((k + n) - 1) - j)) (range n)
                       ∷ map emb-stype-oterm as ^ [ ! , ι ⁰ ])
          (PE.sym (length-map (λ T → (emb-stype-oterm T , 0)) (SU.ctrArgsTypeList i j)))
          (⊢All-ctor-vars as k P ⊢Γ'))

  foldr-Π⁰-stypes-≡∷ : ∀ {Γ} As C D →
    ⊢ Γ →
    (Γ ∙∙ map emb-stype-oterm As) ⊢ C ≡ D ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ foldr Π⁰ C (map emb-stype-oterm As) ≡ foldr Π⁰ D (map emb-stype-oterm As) ∷ U ⁰ ^ [ ! , next ⁰ ]
  foldr-Π⁰-stypes-≡∷ {Γ} TL.[] C D ⊢Γ C≡D = C≡D
  foldr-Π⁰-stypes-≡∷ {Γ} (A TL.∷ As) C D ⊢Γ C≡D =
    Π-cong (λ _ → ⁰min ⁰ , ⁰min ⁰) (λ ())
      (univ (emb-stype-oterm-has-type A ⊢Γ))
      (refl (emb-stype-oterm-has-type A ⊢Γ))
      (foldr-Π⁰-stypes-≡∷ {Γ = Γ ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ]} As C D
        (⊢Γ ∙ univ (emb-stype-oterm-has-type A ⊢Γ)) C≡D)

  length-ctrRecIndices : ∀ i j →
    length (ctrRecIndices i j) PE.≡ SU.ctrRecCount i j
  length-ctrRecIndices i j =
    let as = SU.ctrArgsTypeList i j
    in PE.trans (length-map proj₁
                   (filter (λ jT → SU.ctrArgIsRecursive i (proj₂ jT))
                     (zip (range (length as)) as)))
         (length-filter-rec i as)
    where
    length-filter-rec : ∀ i (as : List SU.Type) →
      length (filter (λ p → SU.ctrArgIsRecursive i (proj₂ p)) (zip (range (length as)) as))
      PE.≡ SU.recCountList i as
    length-filter-rec i TL.[] = PE.refl
    length-filter-rec i (T TL.∷ Ts)
      rewrite zip-range-cons T Ts
      with SU.ctrArgIsRecursive i T
    length-filter-rec i (T TL.∷ Ts) | true
      rewrite filter-map (λ p → SU.ctrArgIsRecursive i (proj₂ p))
                         (λ p → (1+ (proj₁ p) , proj₂ p))
                         (zip (range (length Ts)) Ts)
      = PE.cong 1+
          (PE.trans (length-map (λ p → (1+ (proj₁ p) , proj₂ p))
                       (filter (λ p → SU.ctrArgIsRecursive i (proj₂ p))
                         (zip (range (length Ts)) Ts)))
            (length-filter-rec i Ts))
    length-filter-rec i (T TL.∷ Ts) | false
      rewrite filter-map (λ p → SU.ctrArgIsRecursive i (proj₂ p))
                         (λ p → (1+ (proj₁ p) , proj₂ p))
                         (zip (range (length Ts)) Ts)
      = PE.trans (length-map (λ p → (1+ (proj₁ p) , proj₂ p))
                     (filter (λ p → SU.ctrArgIsRecursive i (proj₂ p))
                       (zip (range (length Ts)) Ts)))
          (length-filter-rec i Ts)

  method≡branch : ∀ {Γ} i P j → ⊢ Γ →
    Γ ⊢ emb-stype-oterm (SU.indRectBranchTy i j P)
      ≡ indRectBranchTy i j (lam (Ind i) ▹ wk1 (emb-stype-oterm P) ^ ¹) ! ⁰
      ^ [ ! , ι ⁰ ]
  method≡branch {Γ} i P j ⊢Γ =
    univ
      (PE.subst₂
        (λ A B → Γ ⊢ A ≡ B ∷ U ⁰ ^ [ ! , next ⁰ ])
        (PE.sym (emb-indRectBranchTy-stype i j P))
        (PE.sym rhs≡)
        (PE.subst
          (λ k' → Γ ⊢ foldr Π⁰ (foldr Π⁰ Pemb (replicate k' Pemb)) (map emb-stype-oterm as)
                        ≡ foldr Π⁰ innerR (map emb-stype-oterm as) ∷ U ⁰ ^ [ ! , next ⁰ ])
          (length-ctrRecIndices i j)
          (foldr-Π⁰-stypes-≡∷ as innerL innerR ⊢Γ inner≡)))
    where
    as = SU.ctrArgsTypeList i j
    Pemb = emb-stype-oterm P
    Pλ = lam (Ind i) ▹ wk1 Pemb ^ ¹
    n = length (ctrArgsTypeList i j)
    k = length (ctrRecIndices i j)
    innerL = foldr Π⁰ Pemb (replicate k Pemb)
    concR = wk1^ (k + n) Pλ ∘ ctr i j (map (λ j → var (((k + n) - 1) - j)) (range n)) ^ ¹
    recs = ctrRecIndices i j
    ihTys = map (λ pj →
              wk1^ (n + proj₂ pj) Pλ ∘ var (((n - 1) - proj₁ pj) + proj₂ pj) ^ ¹)
              (zip recs (range k))
    innerR = foldr Π⁰ concR ihTys
    rhs≡ : indRectBranchTy i j Pλ ! ⁰ PE.≡ foldr Π⁰ innerR (map emb-stype-oterm as)
    rhs≡ = PE.cong (foldr Π⁰ innerR)
             (map-map proj₁ (λ T → (emb-stype-oterm T , 0)) (SU.ctrArgsTypeList i j))
    emb-indRectBranchTy-stype : ∀ i j P →
      emb-stype-oterm (SU.indRectBranchTy i j P) PE.≡
      foldr Π⁰ (foldr Π⁰ (emb-stype-oterm P)
                  (replicate (SU.ctrRecCount i j) (emb-stype-oterm P)))
        (map emb-stype-oterm (SU.ctrArgsTypeList i j))
    emb-indRectBranchTy-stype i j P =
      PE.trans (emb-arrows Ts (SU.arrowRepeat k′ P P))
        (PE.cong (λ B → foldr Π⁰ B (map emb-stype-oterm Ts))
          (emb-arrowRepeat k′ P P))
      where
      Ts = SU.ctrArgsTypeList i j
      k′  = SU.ctrRecCount i j
      emb-arrows : ∀ As B →
        emb-stype-oterm (SU.arrows As B) PE.≡
        foldr Π⁰ (emb-stype-oterm B) (map emb-stype-oterm As)
      emb-arrows TL.[] B = PE.refl
      emb-arrows (A TL.∷ As) B =
        PE.cong (Π⁰ (emb-stype-oterm A)) (emb-arrows As B)
      emb-arrowRepeat : ∀ n A B →
        emb-stype-oterm (SU.arrowRepeat n A B) PE.≡
        foldr Π⁰ (emb-stype-oterm B) (replicate n (emb-stype-oterm A))
      emb-arrowRepeat 0 A B = PE.refl
      emb-arrowRepeat (1+ n) A B =
        PE.cong (Π⁰ (emb-stype-oterm A)) (emb-arrowRepeat n A B)
    inner≡ : (Γ ∙∙ map emb-stype-oterm as) ⊢ innerL ≡ innerR ∷ U ⁰ ^ [ ! , next ⁰ ]
    inner≡ = PE.subst
      (λ k′ → (Γ ∙∙ map emb-stype-oterm as) ⊢
                foldr Π⁰ Pemb (replicate k′ Pemb) ≡ foldr Π⁰ concR ihTys
                ∷ U ⁰ ^ [ ! , next ⁰ ])
      length-ih
      (goIH 0 ihTys (⊢∙∙-stypes as ⊢Γ)
        (PE.trans (PE.cong (λ m → m + 0) length-ih) (plusZero k))
        PE.refl)
      where
      length-ih : length ihTys PE.≡ k
      length-ih = PE.trans (TL.length-map (λ pj →
                    wk1^ (n + proj₂ pj) Pλ ∘ var (((n - 1) - proj₁ pj) + proj₂ pj) ^ ¹)
                    (zip recs (range k)))
                    (TL.length-zip-eq recs (range k) (PE.sym (TL.length-range k)))
      Γ0 = Γ ∙∙ map emb-stype-oterm as
      drop : {A : Set} → Nat → List A → List A
      drop 0 xs = xs
      drop (1+ _) TL.[] = TL.[]
      drop (1+ m) (_ TL.∷ xs) = drop m xs
      drop-map : ∀ {A B} (f : A → B) m xs →
        drop m (map f xs) PE.≡ map f (drop m xs)
      drop-map f 0 xs = PE.refl
      drop-map f (1+ m) TL.[] = PE.refl
      drop-map f (1+ m) (_ TL.∷ xs) = drop-map f m xs
      zip-r-[] : ∀ {A B} (xs : List A) → zip {B = B} xs TL.[] PE.≡ TL.[]
      zip-r-[] TL.[] = PE.refl
      zip-r-[] (_ TL.∷ _) = PE.refl
      drop-zip : ∀ {A B} (xs : List A) (ys : List B) m →
        drop m (zip xs ys) PE.≡ zip (drop m xs) (drop m ys)
      drop-zip xs ys 0 = PE.refl
      drop-zip TL.[] ys (1+ m) = PE.refl
      drop-zip (_ TL.∷ xs) TL.[] (1+ m) = PE.sym (zip-r-[] (drop m xs))
      drop-zip (_ TL.∷ xs) (_ TL.∷ ys) (1+ m) = drop-zip xs ys m
      nthA : {A : Set} → A → List A → Nat → A
      nthA d TL.[] _ = d
      nthA d (x TL.∷ _) 0 = x
      nthA d (_ TL.∷ xs) (1+ m) = nthA d xs m
      nth : List Nat → Nat → Nat
      nth = nthA 0
      drop-nth-cons : ∀ (xs : List Nat) m →
        m << length xs →
        drop m xs PE.≡ nth xs m TL.∷ drop (1+ m) xs
      drop-nth-cons TL.[] m ()
      drop-nth-cons (_ TL.∷ _) 0 _ = PE.refl
      drop-nth-cons (_ TL.∷ xs) (1+ m) (leS p) = drop-nth-cons xs m p
      drop-range : ∀ m ℓ′ → ℓ′ << m →
        drop ℓ′ (range m) PE.≡ ℓ′ TL.∷ drop (1+ ℓ′) (range m)
      drop-range 0 ℓ′ ()
      drop-range (1+ m) 0 _ =
        PE.trans (range-suc m)
          (PE.cong (0 TL.∷_)
            (PE.sym (PE.cong (drop 1) (range-suc m))))
      drop-range (1+ m) (1+ ℓ′) (leS p) =
        PE.trans (PE.cong (drop (1+ ℓ′)) (range-suc m))
          (PE.trans (drop-map 1+ ℓ′ (range m))
            (PE.trans (PE.cong (map 1+) (drop-range m ℓ′ p))
              (PE.cong ((1+ ℓ′) TL.∷_)
                (PE.trans (PE.sym (drop-map 1+ (1+ ℓ′) (range m)))
                  (PE.sym (PE.cong (drop (1+ (1+ ℓ′))) (range-suc m)))))))
      goIH : (ℓ : Nat) (ihs : List Term) →
        ⊢ (Γ0 ∙∙ replicate ℓ Pemb) →
        length ihs + ℓ PE.≡ k →
        ihs PE.≡ drop ℓ ihTys →
        (Γ0 ∙∙ replicate ℓ Pemb) ⊢
          foldr Π⁰ Pemb (replicate (length ihs) Pemb)
          ≡ foldr Π⁰ concR ihs ∷ U ⁰ ^ [ ! , next ⁰ ]
      goIH ℓ TL.[] ⊢Δ eq _ rewrite eq =
        PE.subst
          (λ f → (Γ0 ∙∙ replicate k Pemb) ⊢ Pemb ≡
                   f ∘ ctr i j (map (λ j → var (((k + n) - 1) - j)) (range n)) ^ ¹
                   ∷ U ⁰ ^ [ ! , next ⁰ ])
          (PE.sym (wk1^-Pλ (k + n) i P))
          (sym (β-const-P i P
                 (ctr i j (map (λ j → var (((k + n) - 1) - j)) (range n)))
                 ⊢Δ (⊢-ctr {Γ = Γ} i j k P ⊢Δ)))
      goIH ℓ (ih TL.∷ ihs) ⊢Δ eq ihdrop =
        Π-cong (λ _ → ⁰min ⁰ , ⁰min ⁰) (λ ())
          (univ (emb-stype-oterm-has-type P ⊢Δ))
          (PE.subst
            (λ T → (Γ0 ∙∙ replicate ℓ Pemb) ⊢ Pemb ≡ T ∷ U ⁰ ^ [ ! , next ⁰ ])
            (PE.sym ihEq)
            (sym (PE.subst
              (λ f → (Γ0 ∙∙ replicate ℓ Pemb) ⊢
                       f ∘ var (((n - 1) - nth recs ℓ) + ℓ) ^ ¹
                       ≡ Pemb ∷ U ⁰ ^ [ ! , next ⁰ ])
              (PE.sym (wk1^-Pλ (n + ℓ) i P))
              (β-const-P i P (var (((n - 1) - nth recs ℓ) + ℓ)) ⊢Δ ⊢a))))
          (let eqΔ : ((Γ0 ∙∙ replicate ℓ Pemb) ∙ Pemb ^ [ ! , ι ⁰ ]) PE.≡
                     (Γ0 ∙∙ replicate (1+ ℓ) Pemb)
               eqΔ = PE.trans (∙∙-∷ʳ Γ0 (replicate ℓ Pemb) Pemb)
                       (PE.cong (Γ0 ∙∙_) (replicate-snoc ℓ Pemb))
               ⊢Δ′ = PE.subst ⊢_ eqΔ (⊢Δ ∙ univ (emb-stype-oterm-has-type P ⊢Δ))
           in PE.subst
                (λ Δ → Δ ⊢ foldr Π⁰ Pemb (replicate (length ihs) Pemb)
                         ≡ foldr Π⁰ concR ihs ∷ U ⁰ ^ [ ! , next ⁰ ])
                (PE.sym eqΔ)
                (goIH (1+ ℓ) ihs ⊢Δ′ (PE.trans (plusSuc (length ihs) ℓ) eq)
                  (PE.cong tail′ (PE.trans ihdrop dropEq))))
        where
        head′ : List Term → Term
        head′ TL.[] = var 0
        head′ (x TL.∷ _) = x
        tail′ : List Term → List Term
        tail′ TL.[] = TL.[]
        tail′ (_ TL.∷ xs) = xs
        ℓ<<k : ℓ << k
        ℓ<<k = PE.subst (ℓ <<_) eq (leS (le-plus-left (length ihs) (le-refl ℓ)))
        ihFun = λ pj →
          wk1^ (n + proj₂ pj) Pλ ∘ var (((n - 1) - proj₁ pj) + proj₂ pj) ^ ¹
        dropEq : drop ℓ ihTys PE.≡
          (wk1^ (n + ℓ) Pλ ∘ var (((n - 1) - nth recs ℓ) + ℓ) ^ ¹)
          TL.∷ drop (1+ ℓ) ihTys
        dropEq =
          PE.trans (drop-map ihFun ℓ (zip recs (range k)))
            (PE.trans (PE.cong (map ihFun)
                (PE.trans (drop-zip recs (range k) ℓ)
                  (PE.cong₂ zip (drop-nth-cons recs ℓ ℓ<<k)
                    (drop-range k ℓ ℓ<<k))))
              (PE.cong
                ((wk1^ (n + ℓ) Pλ ∘ var (((n - 1) - nth recs ℓ) + ℓ) ^ ¹) TL.∷_)
                (PE.trans (PE.cong (map ihFun)
                    (PE.sym (drop-zip recs (range k) (1+ ℓ))))
                  (PE.sym (drop-map ihFun (1+ ℓ) (zip recs (range k)))))))
        ihEq : ih PE.≡
          (wk1^ (n + ℓ) Pλ ∘ var (((n - 1) - nth recs ℓ) + ℓ) ^ ¹)
        ihEq = PE.cong head′ (PE.trans ihdrop dropEq)
        repeat-wk1-Ind : ∀ m i′ → repeat wk1 (Ind i′) m PE.≡ Ind i′
        repeat-wk1-Ind 0 i′ = PE.refl
        repeat-wk1-Ind (1+ m) i′ = PE.cong wk1 (repeat-wk1-Ind m i′)
        nth-∈ₗ : ∀ {A} (d : A) xs m → m << length xs → nthA d xs m ∈ₗ xs
        nth-∈ₗ d TL.[] m ()
        nth-∈ₗ d (_ TL.∷ _) 0 _ = hereₗ
        nth-∈ₗ d (_ TL.∷ xs) (1+ m) (leS p) = thereₗ (nth-∈ₗ d xs m p)
        nth-map : ∀ {A B} (f : A → B) (dA : A) (dB : B) xs m →
          m << length xs →
          nthA dB (map f xs) m PE.≡ f (nthA dA xs m)
        nth-map f dA dB TL.[] m ()
        nth-map f dA dB (_ TL.∷ _) 0 _ = PE.refl
        nth-map f dA dB (_ TL.∷ xs) (1+ m) (leS p) = nth-map f dA dB xs m p
        if′ : {A : Set} → Bool → A → A → A
        if′ true x _ = x
        if′ false _ y = y
        if≡if′ : ∀ {A} (b : Bool) (x y : A) →
          (if b then x else y) PE.≡ if′ b x y
        if≡if′ true x y = PE.refl
        if≡if′ false x y = PE.refl
        nth-filter-p : ∀ {A} (p : A → Bool) (d : A) xs m →
          m << length (filter p xs) →
          p (nthA d (filter p xs) m) PE.≡ true
        nth-filter-p p d TL.[] m ()
        nth-filter-p p d (x TL.∷ xs) m lt =
          PE.subst (λ ys → p (nthA d ys m) PE.≡ true)
            (PE.sym (if≡if′ (p x) (x TL.∷ filter p xs) (filter p xs)))
            (aux (p x) PE.refl
              (PE.subst (λ ys → m << length ys)
                (if≡if′ (p x) (x TL.∷ filter p xs) (filter p xs)) lt))
          where
          aux : (b : Bool) → p x PE.≡ b →
            m << length (if′ b (x TL.∷ filter p xs) (filter p xs)) →
            p (nthA d (if′ b (x TL.∷ filter p xs) (filter p xs)) m) PE.≡ true
          aux true eq lt′ = aux-true m lt′
            where
            aux-true : ∀ m′ →
              m′ << length (x TL.∷ filter p xs) →
              p (nthA d (x TL.∷ filter p xs) m′) PE.≡ true
            aux-true 0 _ = eq
            aux-true (1+ m′) (leS lt′) = nth-filter-p p d xs m′ lt′
          aux false eq lt′ = nth-filter-p p d xs m lt′
        zip-nthT : ∀ As p →
          p ∈ₗ zip (range (length As)) As →
          proj₂ p PE.≡ nthA (SU.Ind 0) As (proj₁ p)
        zip-nthT TL.[] p ()
        zip-nthT (A TL.∷ As) p h =
          help (PE.subst (p ∈ₗ_) (zip-range-cons A As) h)
          where
          help : p ∈ₗ
                   ((0 , A) TL.∷ map (λ q → (1+ (proj₁ q) , proj₂ q))
                     (zip (range (length As)) As)) →
                 proj₂ p PE.≡ nthA (SU.Ind 0) (A TL.∷ As) (proj₁ p)
          help hereₗ = PE.refl
          help (thereₗ h′) with
            ∈ₗ-map-inv (λ q → (1+ (proj₁ q) , proj₂ q))
              (zip (range (length As)) As) p h′
          ... | p′ , eq′ , inn =
            PE.trans (PE.cong proj₂ eq′)
              (PE.trans (zip-nthT As p′ inn)
                (PE.sym (PE.cong (nthA (SU.Ind 0) (A TL.∷ As))
                  (PE.cong proj₁ eq′))))
        eqb≡true : ∀ m n′ → eqb m n′ PE.≡ true → m PE.≡ n′
        eqb≡true m n′ q with m ≟ n′
        eqb≡true m n′ q | yes e = e
        eqb≡true m n′ () | no _
        rec-true-Ind : ∀ T → SU.ctrArgIsRecursive i T PE.≡ true →
          T PE.≡ SU.Ind i
        rec-true-Ind (SU.Arrow _ _) ()
        rec-true-Ind (SU.Ind j′) q = PE.cong SU.Ind (eqb≡true j′ i q)
        pairs = zip (range (length as)) as
        recP = λ (jT : Nat × SU.Type) → SU.ctrArgIsRecursive i (proj₂ jT)
        filtered = filter recP pairs
        ℓ<<filtered : ℓ << length filtered
        ℓ<<filtered = PE.subst (ℓ <<_) (length-map proj₁ filtered) ℓ<<k
        pair = nthA (0 , SU.Ind 0) filtered ℓ
        nthT≡Ind : nthA (SU.Ind 0) as (nth recs ℓ) PE.≡ SU.Ind i
        nthT≡Ind =
          PE.trans
            (PE.cong (nthA (SU.Ind 0) as)
              (nth-map proj₁ (0 , SU.Ind 0) 0 filtered ℓ ℓ<<filtered))
            (PE.trans
              (PE.sym (zip-nthT as pair
                (filter-∈ₗ recP pairs pair
                  (nth-∈ₗ (0 , SU.Ind 0) filtered ℓ ℓ<<filtered))))
              (rec-true-Ind (proj₂ pair)
                (nth-filter-p recP (0 , SU.Ind 0) pairs ℓ ℓ<<filtered)))
        n≡len-as : n PE.≡ length as
        n≡len-as = length-map (λ T → (emb-stype-oterm T , 0)) as
        rec<<n : nth recs ℓ << length as
        rec<<n =
          let inn-recs = nth-∈ₗ 0 recs ℓ ℓ<<k
              inv = ∈ₗ-map-inv proj₁ filtered (nth recs ℓ) inn-recs
              inn-zip = filter-∈ₗ recP pairs (proj₁ inv)
                          (proj₂ (proj₂ inv))
              inn-range = PE.subst (λ x → x ∈ₗ range (length as))
                            (PE.sym (proj₁ (proj₂ inv)))
                            (proj₁ (zip-∈ₗ (range (length as)) as
                              (proj₁ inv) inn-zip))
          in ∈ₗ-range (length as) (nth recs ℓ) inn-range
        ∈-ctor-arg : ∀ {Δ} (As : List SU.Type) (idx : Nat) →
          idx << length As →
          nthA (SU.Ind 0) As idx PE.≡ SU.Ind i →
          ((length As - 1) - idx) ∷ Ind i ^ [ ! , ι ⁰ ]
            ∈ (Δ ∙∙ map emb-stype-oterm As)
        ∈-ctor-arg {Δ} TL.[] idx ()
        ∈-ctor-arg {Δ} (A TL.∷ As) 0 _ nthEq =
          PE.subst₂
            (λ idx ty → idx ∷ ty ^ [ ! , ι ⁰ ]
              ∈ ((Δ ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ])
                   ∙∙ map emb-stype-oterm As))
            (PE.trans (plusZero (length (map emb-stype-oterm As)))
              (length-map emb-stype-oterm As))
            (PE.trans
              (PE.cong
                (λ B → repeat wk1 (wk1 (emb-stype-oterm B))
                         (length (map emb-stype-oterm As)))
                nthEq)
              (repeat-wk1-Ind (length (map emb-stype-oterm As)) i))
            (there* (map emb-stype-oterm As) here)
        ∈-ctor-arg {Δ} (A TL.∷ As) (1+ idx) (leS p) nthEq =
          PE.subst
            (λ idx′ → idx′ ∷ Ind i ^ [ ! , ι ⁰ ]
              ∈ ((Δ ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ])
                   ∙∙ map emb-stype-oterm As))
            (PE.sym (minus-suc (length As) idx))
            (∈-ctor-arg {Δ = Δ ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ]}
              As idx p nthEq)
        ∈Γ0 : ((length as - 1) - nth recs ℓ) ∷ Ind i ^ [ ! , ι ⁰ ] ∈ Γ0
        ∈Γ0 = ∈-ctor-arg as (nth recs ℓ) rec<<n nthT≡Ind
        ⊢a : (Γ0 ∙∙ replicate ℓ Pemb) ⊢
               var (((n - 1) - nth recs ℓ) + ℓ) ∷ Ind i ^ [ ! , ι ⁰ ]
        ⊢a = var ⊢Δ
          (PE.subst₂
            (λ idx ty → idx ∷ ty ^ [ ! , ι ⁰ ]
              ∈ (Γ0 ∙∙ replicate ℓ Pemb))
            (PE.trans
              (PE.cong (λ m → m + ((length as - 1) - nth recs ℓ))
                (length-replicate ℓ Pemb))
              (PE.trans
                (plus-comm ℓ ((length as - 1) - nth recs ℓ))
                (PE.cong (λ m → ((m - 1) - nth recs ℓ) + ℓ)
                  (PE.sym n≡len-as))))
            (PE.trans
              (PE.cong (repeat wk1 (Ind i))
                (length-replicate ℓ Pemb))
              (repeat-wk1-Ind ℓ i))
            (there* (replicate ℓ Pemb) ∈Γ0))

  emb-indRectBranchTyList-stype : ∀ {Γ} i P → ⊢ Γ →
    TysEq Γ (map emb-stype-oterm (SU.indRectBranchTypeList i P))
            (indRectBranchTyList i (lam (Ind i) ▹ wk1 (emb-stype-oterm P) ^ ¹) ! ⁰)
            ([ ! , ι ⁰ ])
  emb-indRectBranchTyList-stype {Γ} i P ⊢Γ =
    PE.subst₂ (λ As Bs → TysEq Γ As Bs ([ ! , ι ⁰ ]))
      (PE.sym (map-map emb-stype-oterm (λ j → SU.indRectBranchTy i j P)
                (range (SU.indCtrCount i))))
      PE.refl
      (map-≡tys (range (SU.indCtrCount i)) (λ j → method≡branch i P j ⊢Γ))
    where
    map-≡tys : ∀ {Γ r} {f g : Nat → Term} ns →
      (∀ j → Γ ⊢ f j ≡ g j ^ r) →
      TysEq Γ (map f ns) (map g ns) r
    map-≡tys TL.[] _ = ε
    map-≡tys (n TL.∷ ns) h = cons (h n) (map-≡tys ns h)

  mutual
    go-all : ∀ {Γ args As}
      → Γ ST.⊢All args ∷ As
      → emb-scon Γ ⊢All (emb-sterm-oterm-all args) ∷ map emb-stype-oterm As ^ [ ! , ι ⁰ ]
    go-all ST.εⱼ = εⱼ
    go-all (ST.consⱼ t∈ ts∈) = consⱼ (go t∈) (go-all ts∈)

    go : ∀ {Γ t A}
      → Γ ST.⊢ t ∷ A
      → emb-scon Γ ⊢ emb-sterm-oterm t ∷ emb-stype-oterm A ^ [ ! , ι ⁰ ]
    go (ST.varⱼ h) =
      conv (var (emb-scon-wf _) (emb-st-var∈ h))
           (emb-st-wkTy≡ (emb-st-var-wk-depth h) (emb-scon-wf _))
    go (ST.appⱼ {A = A} {B = B} f∈ a∈) =
      conv (_▹_▹_▹_∘ⱼ_ {F = emb-stype-oterm A} {G = emb-stype-oterm B}
              {lG = ⁰} {r = !} {lΠ = ⁰}
              (λ ())
              (emb-stype-oterm-has-type A (emb-scon-wf _))
              (emb-stype-oterm-has-type B (emb-scon-wf _ ∙ univ (emb-stype-oterm-has-type A (emb-scon-wf _))))
              (go f∈)
              (go a∈))
           (PE.subst (λ (embTy : Term) → emb-scon _ ⊢ emb-stype-oterm B [ emb-sterm-oterm _ ] ≡ embTy ^ [ ! , ι ⁰ ])
                     (emb-stype-subst-id B (sgSubst (emb-sterm-oterm _)))
                     (refl (PE.subst (λ (embTy : Term) → emb-scon _ ⊢ embTy ^ [ ! , ι ⁰ ])
                                    (PE.sym (emb-stype-subst-id B (sgSubst (emb-sterm-oterm _))))
                                    (univ (emb-stype-oterm-has-type B (emb-scon-wf _))))))
    go (ST.lamⱼ {A = A} t∈) =
      lamⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) (λ ())
        (univ (emb-stype-oterm-has-type A (emb-scon-wf _)))
        (go t∈)
    go (ST.ctrⱼ {i} {j} _ _ args∈) =
      Ctrⱼ (emb-scon-wf _) (go-all args∈)
    go {Γ} (ST.indRectⱼ {i} {P} {t} {ms} t∈ ms∈) =
      let ⊢Γ = emb-scon-wf Γ
          ⊢Ind = univ (Indⱼ ⊢Γ)
          ⊢ΓInd = ⊢Γ ∙ ⊢Ind
          Pemb = emb-stype-oterm P
          Pλ = lam (Ind i) ▹ wk1 Pemb ^ ¹
          ⊢Pemb∙ = emb-stype-oterm-has-type P ⊢ΓInd
          ⊢wk1Pemb =
            PE.subst (λ u → emb-scon Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ u ∷ U ⁰ ^ [ ! , next ⁰ ])
              (PE.sym (emb-stype-wk-id P (step id)))
              ⊢Pemb∙
          ⊢Pλ = lamⱼ (λ _ → ⁰min ¹ , ≡is≤ PE.refl) (λ ()) ⊢Ind ⊢wk1Pemb
          ⊢t = go t∈
          ⊢ms = convAll (go-all ms∈) (emb-indRectBranchTyList-stype i P ⊢Γ)
          ⊢elim = IndRectⱼ (λ ()) ⊢Pλ ⊢t ⊢ms
          βeq = β-red (⁰min ¹) (≡is≤ PE.refl) ⊢Ind ⊢wk1Pemb ⊢t
          βty = PE.subst
            (λ T → emb-scon Γ ⊢ Pλ ∘ emb-sterm-oterm t ^ ¹ ≡ T ∷ U ⁰ ^ [ ! , next ⁰ ])
            (PE.trans (PE.cong (λ u → u [ emb-sterm-oterm t ]) (emb-stype-wk-id P (step id)))
              (emb-stype-subst-id P (sgSubst (emb-sterm-oterm t))))
            βeq
      in  conv ⊢elim (univ βty)
