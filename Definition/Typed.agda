{-# OPTIONS --safe #-}

open import Definition.Equiv

module Definition.Typed (equiv : Equiv) where

open import Definition.Untyped hiding (equiv)

open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE
open import Definition.Sort

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
    cast-equiv-fwd : ∀ {e n}
                     → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ2 ^ [ % , ι ⁰ ]
                     → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
                     → Γ ⊢ cast ⁰ ℕ ℕ2 e n
                     ≡ (emb_oterm_term (Equiv.fwd equiv)) ∘ n ^ ⁰
                     ∷ ℕ2 ^ [ ! , ι ⁰ ]
    cast-equiv-bwd : ∀ {e n}
                     → Γ ⊢ e ∷ Id (U ⁰) ℕ2 ℕ ^ [ % , ι ⁰ ]
                     → Γ ⊢ n ∷ ℕ2 ^ [ ! , ι ⁰ ]
                     → Γ ⊢ cast ⁰ ℕ2 ℕ e n
                     ≡ (emb_oterm_term (Equiv.bwd equiv)) ∘ n ^ ⁰
                     ∷ ℕ ^ [ ! , ι ⁰ ]
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

import Definition.OTyped as OT
import Definition.OUntyped as OU

emb-∈ : ∀ {x A r Γ} (h : OT._∷_^_∈_ x A r Γ) →
  x ∷ emb_oterm_term A ^ r ∈ emb_con Γ
emb-∈ (OT.here {Γ = Γ} {A = A} {r = r}) =
  PE.subst (λ t → _∷_^_∈_ 0 t r (_∙_^_ (emb_con Γ) (emb_oterm_term A) r))
    (PE.sym (emb-wk1 A)) here
emb-∈ (OT.there {Γ = Γ} {A = A} {rA = rA} {B = B} {rB = rB} {x = x} h) =
  PE.subst (λ t → _∷_^_∈_ (Nat.suc x) t rA (_∙_^_ (emb_con Γ) (emb_oterm_term B) rB))
    (PE.sym (emb-wk1 A)) (there (emb-∈ h))
  where
  open import Definition.Sort using (_∙_^_)

mutual
  emb-⊢∷-sgType : ∀ {Γ t G r s} (⊢t : OT._⊢_∷_^_ Γ t (G OU.[ s ]) r) →
    emb_con Γ ⊢ emb_oterm_term t ∷ emb_oterm_term G [ emb_oterm_term s ] ^ r
  emb-⊢∷-sgType {Γ} {t} {G} {r} {s} ⊢t =
    PE.subst (λ B → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term t) B r)
      (emb-sgSubst G s) (emb-⊢∷ ⊢t)

  emb-⊢∷-natrec-s : ∀ {Γ G rG lG s} (⊢s : OT._⊢_∷_^_ Γ s (OU.natrecStepType G rG lG) ([ rG , ι lG ])) →
    emb_con Γ ⊢ emb_oterm_term s ∷
      Π ℕ ^ ! ° ⁰ ▹ (emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ ([ rG , ι lG ])
  emb-⊢∷-natrec-s {Γ} {G} {rG} {lG} {s} ⊢s =
    PE.subst (λ A → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term s) A ([ rG , ι lG ]))
      (emb-natrec-s-type G rG lG) (emb-⊢∷ ⊢s)

  emb-⊢∷-natrec2-s : ∀ {Γ G rG lG s} (⊢s : OT._⊢_∷_^_ Γ s (OU.natrec2StepType G rG lG) ([ rG , ι lG ])) →
    emb_con Γ ⊢ emb_oterm_term s ∷
      Π ℕ2 ^ ! ° ⁰ ▹ (emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc2 (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ ([ rG , ι lG ])
  emb-⊢∷-natrec2-s {Γ} {G} {rG} {lG} {s} ⊢s =
    PE.subst (λ A → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term s) A ([ rG , ι lG ]))
      (emb-natrec2-s-type G rG lG) (emb-⊢∷ ⊢s)

  emb-⊢ : ∀ {Γ} → OT.⊢ Γ → ⊢ emb_con Γ
  emb-⊢ OT.ε = ε
  emb-⊢ (OT._∙_ ⊢Γ ⊢A) = emb-⊢ ⊢Γ ∙ emb-⊢ty ⊢A

  emb-⊢ty : ∀ {Γ A r} → OT._⊢_^_ Γ A r → emb_con Γ ⊢ (emb_oterm_term A) ^ r
  emb-⊢ty (OT.Uⱼ ⊢Γ) = Uⱼ (emb-⊢ ⊢Γ)
  emb-⊢ty (OT.univ A) = univ (emb-⊢∷ A)

  emb-⊢∷ : ∀ {Γ t A r} → OT._⊢_∷_^_ Γ t A r
         → emb_con Γ ⊢ emb_oterm_term t ∷ (emb_oterm_term A) ^ r
  emb-⊢∷ (OT.univ <l ⊢Γ) = univ <l (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.ℕⱼ ⊢Γ) = ℕⱼ (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.ℕ2ⱼ ⊢Γ) = ℕ2ⱼ (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.Emptyⱼ ⊢Γ) = Emptyⱼ (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.Πⱼ abs₁ ▹ abs₂ ▹ dom ▹ cod) =
    Πⱼ abs₁ ▹ abs₂ ▹ (emb-⊢∷ dom) ▹ (emb-⊢∷ cod)
  emb-⊢∷ (OT.var ⊢Γ x∈Γ) = var (emb-⊢ ⊢Γ) (emb-∈ x∈Γ)
  emb-⊢∷ (OT.lamⱼ abs₁ abs₂ dom t) =
    lamⱼ abs₁ abs₂ (emb-⊢ty dom) (emb-⊢∷ t)
  emb-⊢∷ {Γ = Γ} (OT._▹_▹_▹_∘ⱼ_ {g = g} {a = a} {F = F} {G = Gₜ} {lG = lG} {r = r} {lΠ = lΠ} abs ⊢F ⊢Gderiv ⊢gderiv ⊢aderiv) =
    PE.subst (λ (A : Term) → emb_con Γ ⊢ emb_oterm_term (g OU.∘ a ^ lΠ) ∷ A ^ [ r , ι lG ])
         (PE.sym (emb-sgSubst Gₜ a))
         (PE.subst (λ (t : Term) → emb_con Γ ⊢ t ∷ emb_oterm_term Gₜ [ emb_oterm_term a ] ^ [ r , ι lG ])
           (emb-∘ g a lΠ)
           (_▹_▹_▹_∘ⱼ_ {G = emb_oterm_term Gₜ} abs (emb-⊢∷ ⊢F) (emb-⊢∷ ⊢Gderiv) (emb-⊢∷ ⊢gderiv) (emb-⊢∷ ⊢aderiv)))
  emb-⊢∷ (OT.fstⱼ A B A' B' e) =
    fstⱼ (emb-⊢∷ A) (emb-⊢∷ B) (emb-⊢∷ A') (emb-⊢∷ B') (emb-⊢∷ e)
  emb-⊢∷ {Γ = Γ} (OT.sndⱼ {A = Aₒ} {A' = A'ₒ} {rA = rA} {B = Bₒ} {B' = B'ₒ} {e = e} ⊢A ⊢B ⊢A' ⊢B' ⊢e) =
    PE.subst (λ (A : Term) → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term (OU.snd e)) A ([ % , ι ⁰ ]))
      (emb-snd-Π-type {Aₒ} {A'ₒ} {rA} {Bₒ} {B'ₒ} e)
      (PE.subst (λ (t : Term) → _⊢_∷_^_ (emb_con Γ) t
                   (Π (emb_oterm_term A'ₒ) ^ rA ° ⁰ ▹ Id (U ⁰)
                     (emb_oterm_term Bₒ [ cast ⁰ (wk1 (emb_oterm_term A'ₒ)) (wk1 (emb_oterm_term Aₒ))
                       (Idsym (Univ rA ⁰) (wk1 (emb_oterm_term Aₒ)) (wk1 (emb_oterm_term A'ₒ))
                         (fst (wk1 (emb_oterm_term e)))) (var 0) ]↑)
                     (emb_oterm_term B'ₒ) ° ⁰ ° ⁰ ^ %)
                   ([ % , ι ⁰ ]))
        (PE.sym (emb-snd e))
        (sndⱼ (emb-⊢∷ ⊢A) (emb-⊢∷ ⊢B) (emb-⊢∷ ⊢A') (emb-⊢∷ ⊢B') (emb-⊢∷ ⊢e)))
  emb-⊢∷ (OT.zeroⱼ ⊢Γ) = zeroⱼ (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.sucⱼ n) = sucⱼ (emb-⊢∷ n)
  emb-⊢∷ (OT.zero2ⱼ ⊢Γ) = zero2ⱼ (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.suc2ⱼ n) = suc2ⱼ (emb-⊢∷ n)
  emb-⊢∷ {Γ = Γ} (OT.natrecⱼ {G = G} {rG = rG} {lG = lG} {s = s} {z = z} {n = n} abs cod ⊢z ⊢s ⊢n) =
    PE.subst (λ A → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec lG G z s n)) A ([ rG , ι lG ]))
      (PE.sym (emb-sgSubst G n))
      (PE.subst (λ t → _⊢_∷_^_ (emb_con Γ) t (emb_oterm_term G [ emb_oterm_term n ]) ([ rG , ι lG ]))
        (PE.sym (emb-natrec lG G z s n))
        (natrecⱼ abs (emb-⊢ty cod) (emb-⊢∷-sgType {G = G} {s = OU.zero} ⊢z) (emb-⊢∷-natrec-s {G = G} ⊢s) (emb-⊢∷ ⊢n)))
  emb-⊢∷ {Γ = Γ} (OT.natrec2ⱼ {G = G} {rG = rG} {lG = lG} {s = s} {z = z} {n = n} abs cod ⊢z ⊢s ⊢n) =
    PE.subst (λ A → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec2 lG G z s n)) A ([ rG , ι lG ]))
      (PE.sym (emb-sgSubst G n))
      (PE.subst (λ t → _⊢_∷_^_ (emb_con Γ) t (emb_oterm_term G [ emb_oterm_term n ]) ([ rG , ι lG ]))
        (PE.sym (emb-natrec2 lG G z s n))
        (natrec2ⱼ abs (emb-⊢ty cod) (emb-⊢∷-sgType {G = G} {s = OU.zero2} ⊢z) (emb-⊢∷-natrec2-s {G = G} ⊢s) (emb-⊢∷ ⊢n)))
  emb-⊢∷ (OT.Emptyrecⱼ A e) = Emptyrecⱼ (emb-⊢ty A) (emb-⊢∷ e)
  emb-⊢∷ (OT.Idⱼ A t u) = Idⱼ (emb-⊢∷ A) (emb-⊢∷ t) (emb-⊢∷ u)
  emb-⊢∷ (OT.Idreflⱼ t) = Idreflⱼ (emb-⊢∷ t)
  emb-⊢∷ {Γ = Γ} (OT.transpⱼ {A = A} {P = P} {t = t} {s = s} {u = u} {e = e} ⊢A ⊢P ⊢t ⊢s ⊢u ⊢e) =
    PE.subst (λ Ty → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term (OU.transp A P t s u e)) Ty ([ % , ι ⁰ ]))
      (PE.sym (emb-sgSubst P u))
      (PE.subst (λ tm → _⊢_∷_^_ (emb_con Γ) tm (emb_oterm_term P [ emb_oterm_term u ]) ([ % , ι ⁰ ]))
        (PE.sym (emb-transp A P t s u e))
        (transpⱼ (emb-⊢ty ⊢A) (emb-⊢ty ⊢P) (emb-⊢∷ ⊢t) (emb-⊢∷-sgType {G = P} {s = t} ⊢s) (emb-⊢∷ ⊢u) (emb-⊢∷ ⊢e)))
  emb-⊢∷ (OT.castⱼ A B e t) =
    castⱼ (emb-⊢∷ A) (emb-⊢∷ B) (emb-⊢∷ e) (emb-⊢∷ t)
  emb-⊢∷ (OT.conv t pAB) = conv (emb-⊢∷ t) (emb-⊢≡ pAB)

  emb-⊢≡ : ∀ {Γ A B r} → OT._⊢_≡_^_ Γ A B r → emb_con Γ ⊢ emb_oterm_term A ≡ emb_oterm_term B ^ r
  emb-⊢≡ (OT.refl A) = refl (emb-⊢ty A)
  emb-⊢≡ (OT.sym pAB) = sym (emb-⊢≡ pAB)
  emb-⊢≡ (OT.trans pAB pBC) = trans (emb-⊢≡ pAB) (emb-⊢≡ pBC)
  emb-⊢≡ (OT.univ pAB) = univ (emb-⊢≡∷ pAB)

  emb-⊢≡∷-sgType : ∀ {Γ t u G s r} (⊢tu : OT._⊢_≡_∷_^_ Γ t u (G OU.[ s ]) r) →
    emb_con Γ ⊢ emb_oterm_term t ≡ emb_oterm_term u ∷ emb_oterm_term G [ emb_oterm_term s ] ^ r
  emb-⊢≡∷-sgType {Γ} {t} {u} {G} {s} {r} ⊢tu =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term t) (emb_oterm_term u) B r)
      (emb-sgSubst G s) (emb-⊢≡∷ ⊢tu)

  emb-⊢≡∷-natrec-s : ∀ {Γ G rG lG s s'} (⊢tu : OT._⊢_≡_∷_^_ Γ s s' (OU.natrecStepType G rG lG) ([ rG , ι lG ])) →
    emb_con Γ ⊢ emb_oterm_term s ≡ emb_oterm_term s' ∷
      Π ℕ ^ ! ° ⁰ ▹ (emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ ([ rG , ι lG ])
  emb-⊢≡∷-natrec-s {Γ} {G} {rG} {lG} {s} {s'} ⊢tu =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term s) (emb_oterm_term s') B ([ rG , ι lG ]))
      (emb-natrec-s-type G rG lG) (emb-⊢≡∷ ⊢tu)

  emb-⊢≡∷-natrec2-s : ∀ {Γ G rG lG s s'} (⊢tu : OT._⊢_≡_∷_^_ Γ s s' (OU.natrec2StepType G rG lG) ([ rG , ι lG ])) →
    emb_con Γ ⊢ emb_oterm_term s ≡ emb_oterm_term s' ∷
      Π ℕ2 ^ ! ° ⁰ ▹ (emb_oterm_term G ^ rG ° lG ▹▹ emb_oterm_term G [ suc2 (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ ([ rG , ι lG ])
  emb-⊢≡∷-natrec2-s {Γ} {G} {rG} {lG} {s} {s'} ⊢tu =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term s) (emb_oterm_term s') B ([ rG , ι lG ]))
      (emb-natrec2-s-type G rG lG) (emb-⊢≡∷ ⊢tu)

  emb-⊢≡∷-natrecEq : ∀ {Γ l F F' z z' s s' n n'}
    (pf : emb_con Γ ⊢ natrec l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)
      ≡ natrec l (emb_oterm_term F') (emb_oterm_term z') (emb_oterm_term s') (emb_oterm_term n')
      ∷ emb_oterm_term F [ emb_oterm_term n ] ^ [ ! , ι l ]) →
    emb_con Γ ⊢ emb_oterm_term (OU.natrec l F z s n)
      ≡ emb_oterm_term (OU.natrec l F' z' s' n')
      ∷ emb_oterm_term (F OU.[ n ]) ^ [ ! , ι l ]
  emb-⊢≡∷-natrecEq {Γ} {l} {F} {F'} {z} {z'} {s} {s'} {n} {n'} pf =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec l F z s n))
                (emb_oterm_term (OU.natrec l F' z' s' n')) B ([ ! , ι l ]))
      (PE.sym (emb-sgSubst F n))
      (PE.subst (λ u → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec l F z s n)) u
                  (emb_oterm_term F [ emb_oterm_term n ]) ([ ! , ι l ]))
        (PE.sym (emb-natrec l F' z' s' n'))
        (PE.subst (λ t → _⊢_≡_∷_^_ (emb_con Γ) t
                    (natrec l (emb_oterm_term F') (emb_oterm_term z') (emb_oterm_term s') (emb_oterm_term n'))
                    (emb_oterm_term F [ emb_oterm_term n ]) ([ ! , ι l ]))
          (PE.sym (emb-natrec l F z s n)) pf))

  emb-⊢≡∷-natrec2Eq : ∀ {Γ l F F' z z' s s' n n'}
    (pf : emb_con Γ ⊢ natrec2 l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)
      ≡ natrec2 l (emb_oterm_term F') (emb_oterm_term z') (emb_oterm_term s') (emb_oterm_term n')
      ∷ emb_oterm_term F [ emb_oterm_term n ] ^ [ ! , ι l ]) →
    emb_con Γ ⊢ emb_oterm_term (OU.natrec2 l F z s n)
      ≡ emb_oterm_term (OU.natrec2 l F' z' s' n')
      ∷ emb_oterm_term (F OU.[ n ]) ^ [ ! , ι l ]
  emb-⊢≡∷-natrec2Eq {Γ} {l} {F} {F'} {z} {z'} {s} {s'} {n} {n'} pf =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec2 l F z s n))
                (emb_oterm_term (OU.natrec2 l F' z' s' n')) B ([ ! , ι l ]))
      (PE.sym (emb-sgSubst F n))
      (PE.subst (λ u → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec2 l F z s n)) u
                  (emb_oterm_term F [ emb_oterm_term n ]) ([ ! , ι l ]))
        (PE.sym (emb-natrec2 l F' z' s' n'))
        (PE.subst (λ t → _⊢_≡_∷_^_ (emb_con Γ) t
                    (natrec2 l (emb_oterm_term F') (emb_oterm_term z') (emb_oterm_term s') (emb_oterm_term n'))
                    (emb_oterm_term F [ emb_oterm_term n ]) ([ ! , ι l ]))
          (PE.sym (emb-natrec2 l F z s n)) pf))

  emb-⊢≡∷-natrecZero : ∀ {Γ l F z s}
    (pf : emb_con Γ ⊢ natrec l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) zero
      ≡ emb_oterm_term z ∷ emb_oterm_term F [ zero ] ^ [ ! , ι l ]) →
    emb_con Γ ⊢ emb_oterm_term (OU.natrec l F z s OU.zero)
      ≡ emb_oterm_term z ∷ emb_oterm_term (F OU.[ OU.zero ]) ^ [ ! , ι l ]
  emb-⊢≡∷-natrecZero {Γ} {l} {F} {z} {s} pf =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec l F z s OU.zero))
                (emb_oterm_term z) B ([ ! , ι l ]))
      (PE.sym (emb-sgSubst F OU.zero))
      (PE.subst (λ t → _⊢_≡_∷_^_ (emb_con Γ) t (emb_oterm_term z)
                  (emb_oterm_term F [ zero ]) ([ ! , ι l ]))
        (PE.sym (emb-natrec l F z s OU.zero))
        pf)

  emb-⊢≡∷-natrecSuc : ∀ {Γ l F z s n}
    (pf : emb_con Γ ⊢ natrec l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (suc (emb_oterm_term n))
      ≡ (emb_oterm_term s ∘ emb_oterm_term n ^ l) ∘ (natrec l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)) ^ l
      ∷ emb_oterm_term F [ suc (emb_oterm_term n) ] ^ [ ! , ι l ]) →
    emb_con Γ ⊢ emb_oterm_term (OU.natrec l F z s (OU.suc n))
      ≡ emb_oterm_term ((s OU.∘ n ^ l) OU.∘ (OU.natrec l F z s n) ^ l)
      ∷ emb_oterm_term (F OU.[ OU.suc n ]) ^ [ ! , ι l ]
  emb-⊢≡∷-natrecSuc {Γ} {l} {F} {z} {s} {n} pf =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec l F z s (OU.suc n)))
                (emb_oterm_term ((s OU.∘ n ^ l) OU.∘ (OU.natrec l F z s n) ^ l)) B ([ ! , ι l ]))
      (PE.sym (emb-sgSubst F (OU.suc n)))
      (PE.subst (λ u → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec l F z s (OU.suc n))) u
                  (emb_oterm_term F [ suc (emb_oterm_term n) ]) ([ ! , ι l ]))
        (PE.sym (emb-natrec-suc-rhs l s n F z))
        (PE.subst (λ t → _⊢_≡_∷_^_ (emb_con Γ) t
                    ((emb_oterm_term s ∘ emb_oterm_term n ^ l) ∘ (natrec l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)) ^ l)
                    (emb_oterm_term F [ suc (emb_oterm_term n) ]) ([ ! , ι l ]))
          (PE.sym (emb-natrec-suc l F z s n))
          pf))

  emb-⊢≡∷-natrec2Zero : ∀ {Γ l F z s}
    (pf : emb_con Γ ⊢ natrec2 l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) zero2
      ≡ emb_oterm_term z ∷ emb_oterm_term F [ zero2 ] ^ [ ! , ι l ]) →
    emb_con Γ ⊢ emb_oterm_term (OU.natrec2 l F z s OU.zero2)
      ≡ emb_oterm_term z ∷ emb_oterm_term (F OU.[ OU.zero2 ]) ^ [ ! , ι l ]
  emb-⊢≡∷-natrec2Zero {Γ} {l} {F} {z} {s} pf =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec2 l F z s OU.zero2))
                (emb_oterm_term z) B ([ ! , ι l ]))
      (PE.sym (emb-sgSubst F OU.zero2))
      (PE.subst (λ t → _⊢_≡_∷_^_ (emb_con Γ) t (emb_oterm_term z)
                  (emb_oterm_term F [ zero2 ]) ([ ! , ι l ]))
        (PE.sym (emb-natrec2 l F z s OU.zero2))
        pf)

  emb-⊢≡∷-natrec2Suc : ∀ {Γ l F z s n}
    (pf : emb_con Γ ⊢ natrec2 l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (suc2 (emb_oterm_term n))
      ≡ (emb_oterm_term s ∘ emb_oterm_term n ^ l) ∘ (natrec2 l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)) ^ l
      ∷ emb_oterm_term F [ suc2 (emb_oterm_term n) ] ^ [ ! , ι l ]) →
    emb_con Γ ⊢ emb_oterm_term (OU.natrec2 l F z s (OU.suc2 n))
      ≡ emb_oterm_term ((s OU.∘ n ^ l) OU.∘ (OU.natrec2 l F z s n) ^ l)
      ∷ emb_oterm_term (F OU.[ OU.suc2 n ]) ^ [ ! , ι l ]
  emb-⊢≡∷-natrec2Suc {Γ} {l} {F} {z} {s} {n} pf =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec2 l F z s (OU.suc2 n)))
                (emb_oterm_term ((s OU.∘ n ^ l) OU.∘ (OU.natrec2 l F z s n) ^ l)) B ([ ! , ι l ]))
      (PE.sym (emb-sgSubst F (OU.suc2 n)))
      (PE.subst (λ u → _⊢_≡_∷_^_ (emb_con Γ) (emb_oterm_term (OU.natrec2 l F z s (OU.suc2 n))) u
                  (emb_oterm_term F [ suc2 (emb_oterm_term n) ]) ([ ! , ι l ]))
        (PE.sym (emb-natrec2-suc-rhs l s n F z))
        (PE.subst (λ t → _⊢_≡_∷_^_ (emb_con Γ) t
                    ((emb_oterm_term s ∘ emb_oterm_term n ^ l) ∘ (natrec2 l (emb_oterm_term F) (emb_oterm_term z) (emb_oterm_term s) (emb_oterm_term n)) ^ l)
                    (emb_oterm_term F [ suc2 (emb_oterm_term n) ]) ([ ! , ι l ]))
          (PE.sym (emb-natrec2-suc l F z s n))
          pf))

  emb-⊢≡∷-ηPremise : ∀ {Γ' f g G l lG} (pf0g0 : OT._⊢_≡_∷_^_ Γ' (OU.wk1 f OU.∘ OU.var Nat.zero ^ l) (OU.wk1 g OU.∘ OU.var Nat.zero ^ l) G ([ ! , ι lG ])) →
    emb_con Γ' ⊢ wk1 (emb_oterm_term f) ∘ var Nat.zero ^ l
      ≡ wk1 (emb_oterm_term g) ∘ var Nat.zero ^ l ∷ emb_oterm_term G ^ [ ! , ι lG ]
  emb-⊢≡∷-ηPremise {Γ' = Γ'} {f = f} {g = g} {G = G} {l = l} {lG = lG} pf0g0 =
    let x' = wk1 (emb_oterm_term f) ∘ var Nat.zero ^ l
    in PE.subst (λ u → emb_con Γ' ⊢ x' ≡ u ∷ emb_oterm_term G ^ [ ! , ι lG ])
         (emb-wk1∘var g l)
         (PE.subst (λ t → emb_con Γ' ⊢ t ≡ emb_oterm_term (OU.wk1 g OU.∘ OU.var Nat.zero ^ l) ∷ emb_oterm_term G ^ [ ! , ι lG ])
           (emb-wk1∘var f l)
           (emb-⊢≡∷ pf0g0))

  emb-⊢≡∷ : ∀ {Γ t u A r} → OT._⊢_≡_∷_^_ Γ t u A r
           → emb_con Γ ⊢ emb_oterm_term t ≡ emb_oterm_term u ∷ (emb_oterm_term A) ^ r
  emb-⊢≡∷ (OT.refl t) = refl (emb-⊢∷ t)
  emb-⊢≡∷ (OT.sym ptu) = sym (emb-⊢≡∷ ptu)
  emb-⊢≡∷ (OT.trans ptu puv) = trans (emb-⊢≡∷ ptu) (emb-⊢≡∷ puv)
  emb-⊢≡∷ (OT.conv ptu pAB) = conv (emb-⊢≡∷ ptu) (emb-⊢≡ pAB)
  emb-⊢≡∷ (OT.Π-cong abs₁ abs₂ dom⊢ pDomH pCodE) =
    Π-cong abs₁ abs₂ (emb-⊢ty dom⊢) (emb-⊢≡∷ pDomH) (emb-⊢≡∷ pCodE)
  emb-⊢≡∷ {Γ = Γ} (OT.app-cong {a = a} {G = G} {lG = lG} pfg pab) =
    let pf = app-cong (emb-⊢≡∷ pfg) (emb-⊢≡∷ pab)
    in PE.subst (λ (B : Term) → emb_con Γ ⊢ _ ≡ _ ∷ B ^ [ ! , ι lG ])
         (PE.sym (emb-sgSubst G a))
         pf
  emb-⊢≡∷ {Γ = Γ} (OT.β-red {a = a} {t = t} {G = G} {lG = lG} lF≤l lG≤l dom⊢ t₁ a₁) =
    let pf = β-red lF≤l lG≤l (emb-⊢ty dom⊢) (emb-⊢∷ t₁) (emb-⊢∷ a₁)
        lhs = (lam _ ▹ emb_oterm_term t ^ _) ∘ emb_oterm_term a ^ _
    in PE.subst (λ (B : Term) → emb_con Γ ⊢ lhs ≡ emb_oterm_term (t OU.[ a ]) ∷ B ^ [ ! , ι lG ])
         (PE.sym (emb-sgSubst G a))
         (PE.subst (λ (u : Term) → emb_con Γ ⊢ lhs ≡ u ∷ emb_oterm_term G [ emb_oterm_term a ] ^ [ ! , ι lG ])
           (PE.sym (emb-sgSubst t a))
           pf)
  emb-⊢≡∷ (OT.η-eq lF≤l lG≤l dom⊢ f g pf0g0) =
    η-eq lF≤l lG≤l (emb-⊢ty dom⊢) (emb-⊢∷ f) (emb-⊢∷ g) (emb-⊢≡∷-ηPremise pf0g0)
  emb-⊢≡∷ (OT.suc-cong n) = suc-cong (emb-⊢≡∷ n)
  emb-⊢≡∷ (OT.suc2-cong n) = suc2-cong (emb-⊢≡∷ n)
  emb-⊢≡∷ (OT.natrec-cong {F = F} pFF' pzz' pss' pnn') =
    emb-⊢≡∷-natrecEq (natrec-cong (emb-⊢≡ pFF')
      (emb-⊢≡∷-sgType {G = F} {s = OU.zero} pzz')
      (emb-⊢≡∷-natrec-s pss') (emb-⊢≡∷ pnn'))
  emb-⊢≡∷ (OT.natrec2-cong {F = F} pFF' pzz' pss' pnn') =
    emb-⊢≡∷-natrec2Eq (natrec2-cong (emb-⊢≡ pFF')
      (emb-⊢≡∷-sgType {G = F} {s = OU.zero2} pzz')
      (emb-⊢≡∷-natrec2-s pss') (emb-⊢≡∷ pnn'))
  emb-⊢≡∷ (OT.natrec-zero {F = F} dom⊢ z s) =
    emb-⊢≡∷-natrecZero (natrec-zero (emb-⊢ty dom⊢)
      (emb-⊢∷-sgType {G = F} {s = OU.zero} z) (emb-⊢∷-natrec-s s))
  emb-⊢≡∷ (OT.natrec-suc {F = F} n dom⊢ z s) =
    emb-⊢≡∷-natrecSuc (natrec-suc (emb-⊢∷ n) (emb-⊢ty dom⊢)
      (emb-⊢∷-sgType {G = F} {s = OU.zero} z) (emb-⊢∷-natrec-s s))
  emb-⊢≡∷ (OT.natrec2-zero {F = F} dom⊢ z s) =
    emb-⊢≡∷-natrec2Zero (natrec2-zero (emb-⊢ty dom⊢)
      (emb-⊢∷-sgType {G = F} {s = OU.zero2} z) (emb-⊢∷-natrec2-s s))
  emb-⊢≡∷ (OT.natrec2-suc {F = F} n dom⊢ z s) =
    emb-⊢≡∷-natrec2Suc (natrec2-suc (emb-⊢∷ n) (emb-⊢ty dom⊢)
      (emb-⊢∷-sgType {G = F} {s = OU.zero2} z) (emb-⊢∷-natrec2-s s))
  emb-⊢≡∷ (OT.Emptyrec-cong pAA' e e') =
    Emptyrec-cong (emb-⊢≡ pAA') (emb-⊢∷ e) (emb-⊢∷ e')
  emb-⊢≡∷ (OT.proof-irrelevance t u) =
    proof-irrelevance (emb-⊢∷ t) (emb-⊢∷ u)
  emb-⊢≡∷ (OT.Id-cong pAA' ptt' puu') =
    Id-cong (emb-⊢≡∷ pAA') (emb-⊢≡∷ ptt') (emb-⊢≡∷ puu')
  emb-⊢≡∷ (OT.cast-refl pAB e t) =
    cast-refl (emb-⊢≡∷ pAB) (emb-⊢∷ e) (emb-⊢∷ t)
  emb-⊢≡∷ (OT.cast-cong pAA' pBB' ptt' e e') =
    cast-cong (emb-⊢≡∷ pAA') (emb-⊢≡∷ pBB') (emb-⊢≡∷ ptt') (emb-⊢∷ e) (emb-⊢∷ e')
  emb-⊢≡∷ {Γ = Γ} (OT.cast-Π {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} {f = f} ⊢A ⊢B ⊢A' ⊢B' ⊢e ⊢f) =
    let l   = ⁰
        LHS = emb_oterm_term (OU.cast l (OU.Π A ^ rA ° l ▹ B ° l ° l ^ !) (OU.Π A' ^ rA ° l ▹ B' ° l ° l ^ !) e f)
        pf  = cast-Π (emb-⊢∷ ⊢A) (emb-⊢∷ ⊢B) (emb-⊢∷ ⊢A') (emb-⊢∷ ⊢B') (emb-⊢∷ ⊢e) (emb-⊢∷ ⊢f)
    in PE.subst (λ rhs → emb_con Γ ⊢ LHS ≡ rhs ∷ (emb_oterm_term (OU.Π A' ^ rA ° l ▹ B' ° l ° l ^ !)) ^ [ ! , ι l ])
         (PE.sym (emb-castΠ-lamBody {A} {A'} {rA} {B} {B'} {e} {f}))
         pf
  emb-⊢≡∷ (OT.cast-ℕ-0 e) = cast-ℕ-0 (emb-⊢∷ e)
  emb-⊢≡∷ (OT.cast-ℕ-S e n) = cast-ℕ-S (emb-⊢∷ e) (emb-⊢∷ n)
