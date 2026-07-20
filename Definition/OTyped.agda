module Definition.OTyped where
open import Definition.OUntyped
open import Tools.Nat using (Nat)
import Agda.Builtin.Nat as BuiltinNat
open import Tools.Product
open import Tools.Empty
open import Tools.List using (List; map)
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
           → Γ ⊢All args ∷ map emb-stype-oterm (SU.ctrArgsTypeList i j)
           → Γ ⊢ ctr i j args ∷ Ind i ^ [ ! , ι ⁰ ]
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
  data _⊢All_∷_ (Γ : Con Term) : List Term → List Term → Set where
    εⱼ   : Γ ⊢All TL.[] ∷ TL.[]
    consⱼ  : ∀ {t ts A As}
         → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
         → Γ ⊢All ts ∷ As
         → Γ ⊢All (t TL.∷ ts) ∷ (A TL.∷ As)

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

emb-stype-oterm-has-type : ∀ (A : SU.Type) {Γ} → ⊢ Γ → Γ ⊢ emb-stype-oterm A ∷ U ⁰ ^ [ ! , next ⁰ ]
emb-stype-oterm-has-type (SU.Ind n) ⊢Γ = Indⱼ ⊢Γ
emb-stype-oterm-has-type (SU.Arrow A B) ⊢Γ =
  Πⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) ▹ (λ ()) ▹ (emb-stype-oterm-has-type A ⊢Γ)
     ▹ (emb-stype-oterm-has-type B (⊢Γ ∙ univ (emb-stype-oterm-has-type A ⊢Γ)))

emb-stype-oterm-wf : ∀ (A : SU.Type) {Γ} → ⊢ Γ → Γ ⊢ emb-stype-oterm A ^ [ ! , ι ⁰ ]
emb-stype-oterm-wf A ⊢Γ = univ (emb-stype-oterm-has-type A ⊢Γ)

emb-scon-wf : ∀ Γ → ⊢ (emb-scon Γ)
emb-scon-wf TL.[] = ε
emb-scon-wf (A TL.∷ Γ) = emb-scon-wf Γ ∙ emb-stype-oterm-wf A (emb-scon-wf Γ)

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
emb-stype-wk1n-id A BuiltinNat.zero = PE.refl
emb-stype-wk1n-id A (BuiltinNat.suc n) =
  PE.trans (PE.cong wk1 (emb-stype-wk1n-id A n)) (emb-stype-wk-id A (step id))

emb-st-var-wk-depth : ∀ {x A Γ} → x ST.∷ A ∈ Γ → Nat
emb-st-var-wk-depth ST.here = 1
emb-st-var-wk-depth (ST.there h) = BuiltinNat.suc (emb-st-var-wk-depth h)

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
                         (emb-stype-oterm-wf A ⊢Γ)))

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

emb-stype-[·]-id : ∀ A t → emb-stype-oterm A [ t ] PE.≡ emb-stype-oterm A
emb-stype-[·]-id A t = emb-stype-subst-id A (sgSubst t)

mutual
  emb-sterm-oterm-preserves-typing-all : ∀ {Γ args As}
    → Γ ST.⊢All args ∷ As
    → emb-scon Γ ⊢All (emb-sterm-oterm-all args) ∷ map emb-stype-oterm As
  emb-sterm-oterm-preserves-typing-all ST.εⱼ = εⱼ
  emb-sterm-oterm-preserves-typing-all (ST.consⱼ t∈ ts∈) =
    consⱼ (emb-sterm-oterm-preserves-typing t∈) (emb-sterm-oterm-preserves-typing-all ts∈)

  emb-sterm-oterm-preserves-typing : ∀ {Γ t A}
    → Γ ST.⊢ t ∷ A
    → emb-scon Γ ⊢ emb-sterm-oterm t ∷ emb-stype-oterm A ^ [ ! , ι ⁰ ]
  emb-sterm-oterm-preserves-typing (ST.varⱼ h) =
    conv (var (emb-scon-wf _) (emb-st-var∈ h))
         (emb-st-wkTy≡ (emb-st-var-wk-depth h) (emb-scon-wf _))
  emb-sterm-oterm-preserves-typing (ST.appⱼ {A = A} {B = B} f∈ a∈) =
    conv (_▹_▹_▹_∘ⱼ_ {F = emb-stype-oterm A} {G = emb-stype-oterm B}
            {lG = ⁰} {r = !} {lΠ = ⁰}
            (λ ())
            (emb-stype-oterm-has-type A (emb-scon-wf _))
            (emb-stype-oterm-has-type B (emb-scon-wf _ ∙ emb-stype-oterm-wf A (emb-scon-wf _)))
            (emb-sterm-oterm-preserves-typing f∈)
            (emb-sterm-oterm-preserves-typing a∈))
         (PE.subst (λ (embTy : Term) → emb-scon _ ⊢ emb-stype-oterm B [ emb-sterm-oterm _ ] ≡ embTy ^ [ ! , ι ⁰ ])
                   (emb-stype-[·]-id B (emb-sterm-oterm _))
                   (refl (PE.subst (λ (embTy : Term) → emb-scon _ ⊢ embTy ^ [ ! , ι ⁰ ])
                                  (PE.sym (emb-stype-[·]-id B (emb-sterm-oterm _)))
                                  (emb-stype-oterm-wf B (emb-scon-wf _)))))
  emb-sterm-oterm-preserves-typing (ST.lamⱼ {A = A} t∈) =
    lamⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) (λ ())
      (emb-stype-oterm-wf A (emb-scon-wf _))
      (emb-sterm-oterm-preserves-typing t∈)
  emb-sterm-oterm-preserves-typing (ST.ctrⱼ args∈) =
    Ctrⱼ (emb-sterm-oterm-preserves-typing-all args∈)