import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed (senv : SI.SEnv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Tools.Nat using (Nat; _<<_)
open import Tools.Product
open import Tools.Empty
open import Tools.List using (List; map; All; All₂; All₃; nth; _++_; length; _∈ₗ_)
import Tools.List as TL
import Tools.PropositionalEquality as PE
open import Tools.Maybe using (just)
import Definition.SUntyped as SU
import Definition.OUntyped senv as OU
import Definition.Equiv senv as Eq
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
    Indⱼ    : ∀ {ind} → ⊢ Γ → ind ∈ₗ senv → Γ ⊢ Ind (SU.SInd.name ind) ∷ U ⁰ ^ [ ! , ι ¹ ]
    Ctrⱼ    : ∀ {ind j args Ts}
           → ⊢ Γ
           → ind ∈ₗ senv
           → SU.ctrArgsTypeList ind j PE.≡ just Ts
           → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
           → Γ ⊢ ctr (SU.SInd.name ind) j args ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
    IndRectⱼ : ∀ {ind P rG lG t ms}
           → (rG PE.≡ % → lG PE.≡ ⁰)
           → ind ∈ₗ senv
           → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ^ [ rG , ι lG ]
           → Γ ⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
           → Γ ⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ]
           → Γ ⊢ IndRect (SU.SInd.name ind) lG P t ms ∷ P [ t ] ^ [ rG , ι lG ]
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
    equiv-eqⱼ : ∀ {n e}
              → ⊢ Γ
              → (nth equivs n PE.≡ just e)
              → Γ ⊢ equiv-eq n ∷ Id (U ⁰) (Ind (E.Equiv.indA e)) (Ind (E.Equiv.indB e)) ^ [ % , ι ⁰ ]

  -- Well-typed lists of terms
  data _⊢All_∷_^_ (Γ : Con Term) : List Term → List Term → TypeInfo → Set where
    εⱼ   : ∀ {r} → Γ ⊢All TL.[] ∷ TL.[] ^ r
    consⱼ  : ∀ {t ts A As r}
         → Γ ⊢ t ∷ A ^ r
         → Γ ⊢All ts ∷ As ^ r
         → Γ ⊢All (t TL.∷ ts) ∷ (A TL.∷ As) ^ r

  -- Pointwise conversion of lists of terms
  data _⊢All_≡_∷_^_ (Γ : Con Term) : List Term → List Term → List Term → TypeInfo → Set where
    εⱼ   : ∀ {r} → Γ ⊢All TL.[] ≡ TL.[] ∷ TL.[] ^ r
    consⱼ  : ∀ {t t′ ts ts′ A As r}
         → Γ ⊢ t ≡ t′ ∷ A ^ r
         → Γ ⊢All ts ≡ ts′ ∷ As ^ r
         → Γ ⊢All (t TL.∷ ts) ≡ (t′ TL.∷ ts′) ∷ (A TL.∷ As) ^ r

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
    ctr-cong    : ∀ {ind j args args' Ts}
                → ⊢ Γ
                → ind ∈ₗ senv
                → SU.ctrArgsTypeList ind j PE.≡ just Ts
                → All₃ (λ a a' A → Γ ⊢ a ≡ a' ∷ A ^ [ ! , ι ⁰ ]) args args' (map emb-stype Ts)
                → Γ ⊢ ctr (SU.SInd.name ind) j args ≡ ctr (SU.SInd.name ind) j args' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
    IndRect-cong : ∀ {ind P P' lG t t' ms ms'}
                → ind ∈ₗ senv
                → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ≡ P' ^ [ ! , ι lG ]
                → Γ ⊢ t ≡ t' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
                → Γ ⊢All ms ≡ ms' ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
                → Γ ⊢ IndRect (SU.SInd.name ind) lG P t ms ≡ IndRect (SU.SInd.name ind) lG P' t' ms' ∷ P [ t ] ^ [ ! , ι lG ]
    IndRect-ctr≡ : ∀ {ind j P lG args ms m Ts}
                → ind ∈ₗ senv
                → SU.ctrArgsTypeList ind j PE.≡ just Ts
                → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ^ [ ! , ι lG ]
                → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
                → Γ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
                → nth ms j PE.≡ just m
                → Γ ⊢ IndRect (SU.SInd.name ind) lG P (ctr (SU.SInd.name ind) j args) ms
                    ≡ apps lG m
                             (args ++ map (λ a → IndRect (SU.SInd.name ind) lG P a ms)
                                     (ctrRecArgs (SU.SInd.name ind) Ts args))
                    ∷ P [ ctr (SU.SInd.name ind) j args ] ^ [ ! , ι lG ]
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
    cast-Ind-ctr : ∀ {ind e t}
               → ind ∈ₗ senv
               → Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ]
               → Γ ⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e t
                   ≡ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
    -- There is an equivalence between A and B iff they have the same
    -- representative; cast then computes to its forward function.
    cast-equiv : ∀ {A B e t}
               → (A∈ : A ∈ₗ SU.indNames senv)
               → (B∈ : B ∈ₗ SU.indNames senv)
               → A PE.≢ B
               → (H : reprInd A PE.≡ reprInd B)
               → Γ ⊢ e ∷ Id (U ⁰) (Ind A) (Ind B) ^ [ % , ι ⁰ ]
               → Γ ⊢ t ∷ Ind A ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ (Ind A) (Ind B) e t
                   ≡ emb_oterm_term (Eq.fwdₒ (Eq.repr-equiv equivs A B A∈ B∈ H)) ∘ t ^ ⁰
                   ∷ Ind B ^ [ ! , ι ⁰ ]

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
    IndRect-subst : ∀ {ind P lG t t' ms}
                 → ind ∈ₗ senv
                 → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ^ [ ! , ι lG ]
                 → Γ ⊢ t ⇒ t' ∷ Ind (SU.SInd.name ind) ^ ι ⁰
                 → Γ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
                 → Γ ⊢ IndRect (SU.SInd.name ind) lG P t ms ⇒ IndRect (SU.SInd.name ind) lG P t' ms ∷ P [ t ] ^ ι lG
    -- β: positivity ⇒ all ctor args are recursive Ind (SU.SInd.name ind)
    IndRect-ctr : ∀ {ind j P lG args ms m Ts}
                 → ind ∈ₗ senv
                 → SU.ctrArgsTypeList ind j PE.≡ just Ts
                 → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P ^ [ ! , ι lG ]
                 → Γ ⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
                 → Γ ⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
                 → nth ms j PE.≡ just m
                 → Γ ⊢ IndRect (SU.SInd.name ind) lG P (ctr (SU.SInd.name ind) j args) ms
                     ⇒ apps lG m
                              (args ++ map (λ a → IndRect (SU.SInd.name ind) lG P a ms)
                                     (ctrRecArgs (SU.SInd.name ind) Ts args))
                     ∷ P [ ctr (SU.SInd.name ind) j args ] ^ ι lG
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
    cast-Ind-subst : ∀ {ind B B' e t}
                  → ind ∈ₗ senv
                  → Γ ⊢ B ⇒ B' ∷ U ⁰ ^ next ⁰
                  → Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) B ^ [ % , ι ⁰ ]
                  → Γ ⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
                  → Γ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) B e t ⇒ cast ⁰ (Ind (SU.SInd.name ind)) B' e t ∷ B ^ ι ⁰
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


    cast-Ind-ctr : ∀ {ind e t}
               → ind ∈ₗ senv
               → Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ]
               → Γ ⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e t
                   ⇒ t ∷ Ind (SU.SInd.name ind) ^ ι ⁰

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
    -- A cast between distinct inductives with the same representative
    -- computes to the forward function of the equivalence between them.
    cast-equiv : ∀ {A B e t}
               → (A∈ : A ∈ₗ SU.indNames senv)
               → (B∈ : B ∈ₗ SU.indNames senv)
               → A PE.≢ B
               → (H : reprInd A PE.≡ reprInd B)
               → Γ ⊢ e ∷ Id (U ⁰) (Ind A) (Ind B) ^ [ % , ι ⁰ ]
               → Γ ⊢ t ∷ Ind A ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ (Ind A) (Ind B) e t
                   ⇒ emb_oterm_term (Eq.fwdₒ (Eq.repr-equiv equivs A B A∈ B∈ H)) ∘ t ^ ⁰
                   ∷ Ind B ^ ι ⁰
    
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

import Definition.OTyped senv as OT
emb-∈ : ∀ {x A r Γ} (h : OT._∷_^_∈_ x A r Γ) →
  x ∷ emb_oterm_term A ^ r ∈ emb_con Γ
emb-∈ (OT.here {Γ = Γ} {A = A} {r = r}) =
  PE.subst (λ t → _∷_^_∈_ 0 t r (_∙_^_ (emb_con Γ) (emb_oterm_term A) r))
    (PE.sym (emb-wk1 A)) here
emb-∈ (OT.there {Γ = Γ} {A = A} {rA = rA} {B = B} {rB = rB} {x = x} h) =
  PE.subst (λ t → _∷_^_∈_ (Nat.suc x) t rA (_∙_^_ (emb_con Γ) (emb_oterm_term B) rB))
    (PE.sym (emb-wk1 A)) (there (emb-∈ h))

mutual
  emb-⊢∷-sgType : ∀ {Γ t G r s} (⊢t : OT._⊢_∷_^_ Γ t (G OU.[ s ]) r) →
    emb_con Γ ⊢ emb_oterm_term t ∷ emb_oterm_term G [ emb_oterm_term s ] ^ r
  emb-⊢∷-sgType {Γ} {t} {G} {r} {s} ⊢t =
    PE.subst (λ B → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term t) B r)
      (emb-sgSubst G s) (emb-⊢∷ ⊢t)


  emb-⊢All : ∀ {Γ args As r} → OT._⊢All_∷_^_ Γ args As r
    → emb_con Γ ⊢All emb-oterm-all args ∷ map emb_oterm_term As ^ r
  emb-⊢All OT.εⱼ = εⱼ
  emb-⊢All (OT.consⱼ ⊢t ⊢ts) = consⱼ (emb-⊢∷ ⊢t) (emb-⊢All ⊢ts)

  emb-⊢ : ∀ {Γ} → OT.⊢ Γ → ⊢ emb_con Γ
  emb-⊢ OT.ε = ε
  emb-⊢ (OT._∙_ ⊢Γ ⊢A) = emb-⊢ ⊢Γ ∙ emb-⊢ty ⊢A

  emb-⊢ty : ∀ {Γ A r} → OT._⊢_^_ Γ A r → emb_con Γ ⊢ (emb_oterm_term A) ^ r
  emb-⊢ty (OT.Uⱼ ⊢Γ) = Uⱼ (emb-⊢ ⊢Γ)
  emb-⊢ty (OT.univ A) = univ (emb-⊢∷ A)

  emb-⊢∷ : ∀ {Γ t A r} → OT._⊢_∷_^_ Γ t A r
         → emb_con Γ ⊢ emb_oterm_term t ∷ (emb_oterm_term A) ^ r
  emb-⊢∷ (OT.univ <l ⊢Γ) = univ <l (emb-⊢ ⊢Γ)
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
  emb-⊢∷ (OT.Indⱼ ⊢Γ ind∈) = Indⱼ (emb-⊢ ⊢Γ) ind∈
  emb-⊢∷ {Γ = Γ} (OT.Ctrⱼ {ind} {j} {args} {Ts} ⊢Γ ind∈ eq args∈) =
    PE.subst (λ t → _⊢_∷_^_ (emb_con Γ) t (Ind (SU.SInd.name ind)) ([ ! , ι ⁰ ]))
      (PE.sym (emb-ctr (SU.SInd.name ind) j args))
      (Ctrⱼ (emb-⊢ ⊢Γ) ind∈ eq (PE.subst (λ As → emb_con Γ ⊢All map emb_oterm_term args ∷ As ^ [ ! , ι ⁰ ])
                     (PE.trans (map-map emb_oterm_term OU.emb-stype-oterm (Ts))
                       (map-cong (Ts) emb-stype-hom))
                     (PE.subst (λ ts → emb_con Γ ⊢All ts ∷ map emb_oterm_term (map OU.emb-stype-oterm (Ts)) ^ [ ! , ι ⁰ ])
                              (emb-oterm-all-map args)
                              (emb-⊢All args∈))))
  emb-⊢∷ {Γ = Γ} (OT.IndRectⱼ {ind} {P} {rG} {lG} {t} {ms} abs ind∈ ⊢P ⊢t ⊢ms) =
    PE.subst (λ Ty → _⊢_∷_^_ (emb_con Γ) (emb_oterm_term (OU.IndRect (SU.SInd.name ind) lG P t ms)) Ty ([ rG , ι lG ]))
      (PE.sym (emb-sgSubst P t))
      (PE.subst (λ tm → _⊢_∷_^_ (emb_con Γ) tm (emb_oterm_term P [ emb_oterm_term t ]) ([ rG , ι lG ]))
        (PE.sym (emb-IndRect (SU.SInd.name ind) lG P t ms))
        (IndRectⱼ abs ind∈ (emb-⊢ty ⊢P) (emb-⊢∷ ⊢t)
          (PE.subst (λ As → emb_con Γ ⊢All emb-oterm-all ms ∷ As ^ [ rG , ι lG ])
                    (emb-indRectBranchTyList ind P rG lG)
                    (emb-⊢All ⊢ms))))
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
  emb-⊢≡∷ (OT.cast-Ind-ctr ind∈ ⊢e ⊢t) = cast-Ind-ctr ind∈ (emb-⊢∷ ⊢e) (emb-⊢∷ ⊢t)

-- Nat as a generic inductive, matching Uniquevalence.uty NatExample.
-- Motive P is a function Γ ⊢ P ∷ Π (Ind nat_ind) (Univ rG lG).
module NatExample
  (nat_ind : SU.SInd)
  (nat∈ : nat_ind ∈ₗ senv)
  (nat_ctrs : SU.SInd.ctrArgsTypes nat_ind
              PE.≡ TL.[] TL.∷ (SU.Ind (SU.SInd.name nat_ind) TL.∷ TL.[]) TL.∷ TL.[])
  where

  open import Tools.Nat using (_≟_; 1+; _+_; _-_)
  open import Tools.Nullary using (yes; no)
  open TL using (range)

  natName : Nat
  natName = SU.SInd.name nat_ind

  Zero : Term
  Zero = ctr natName 0 TL.[]

  -- Method type for O: just P [ Zero ].
  nat-method-ty-Zero : ∀ P rG lG →
    indRectBranchTy natName 0 TL.[] P rG lG PE.≡ P [ Zero ]
  nat-method-ty-Zero P rG lG = PE.refl

  ≟-refl : (n : Nat) → (n ≟ n) PE.≡ yes PE.refl
  ≟-refl 0 = PE.refl
  ≟-refl (1+ n) with n ≟ n | ≟-refl n
  ... | yes PE.refl | PE.refl = PE.refl
  ... | no p | _ = ⊥-elim (p PE.refl)

  -- Method type for S: Π (n : Ind). Π (ih : P [ n ]). P [ S n ].
  nat-method-ty-Succ : ∀ P rG lG →
    indRectBranchTy natName 1 (SU.Ind natName TL.∷ TL.[]) P rG lG PE.≡
    Π Ind natName ^ ! ° ⁰ ▹
      (Π (P [ var 0 ]↑) ^ rG ° lG ▹
         P [ ctr natName 1 (var 1 TL.∷ TL.[]) ]↑^ 2
       ° lG ° lG ^ rG)
    ° lG ° lG ^ rG
  nat-method-ty-Succ P rG lG rewrite ≟-refl natName = PE.refl

  indRectBranchTyList-nat : ∀ P rG lG →
    indRectBranchTyList nat_ind P rG lG PE.≡
    (P [ Zero ]) TL.∷
    (Π Ind natName ^ ! ° ⁰ ▹
      (Π (P [ var 0 ]↑) ^ rG ° lG ▹
         P [ ctr natName 1 (var 1 TL.∷ TL.[]) ]↑^ 2
       ° lG ° lG ^ rG)
     ° lG ° lG ^ rG) TL.∷
    TL.[]
  indRectBranchTyList-nat P rG lG =
    PE.trans
      (PE.cong
        (λ Tss → map (λ jTs → indRectBranchTy natName (proj₁ jTs) (proj₂ jTs) P rG lG)
                     (TL.zip (range (length Tss)) Tss))
        nat_ctrs)
      (PE.cong₂ TL._∷_ (nat-method-ty-Zero P rG lG)
        (PE.cong (λ A → A TL.∷ TL.[] ) (nat-method-ty-Succ P rG lG)))

  ⊢-nat-IndRect : ∀ {Γ P rG lG t z s} →
    (rG PE.≡ % → lG PE.≡ ⁰) →
    Γ ∙ Ind natName ^ [ ! , ι ⁰ ] ⊢ P ^ [ rG , ι lG ] →
    Γ ⊢ t ∷ Ind natName ^ [ ! , ι ⁰ ] →
    Γ ⊢ z ∷ (P [ Zero ]) ^ [ rG , ι lG ] →
    Γ ⊢ s ∷
      Π Ind natName ^ ! ° ⁰ ▹
        (Π (P [ var 0 ]↑) ^ rG ° lG ▹
           P [ ctr natName 1 (var 1 TL.∷ TL.[]) ]↑^ 2
         ° lG ° lG ^ rG)
      ° lG ° lG ^ rG
      ^ [ rG , ι lG ] →
    Γ ⊢ IndRect natName lG P t (z TL.∷ s TL.∷ TL.[]) ∷ P [ t ] ^ [ rG , ι lG ]
  ⊢-nat-IndRect {Γ} {P} {rG} {lG} {t} {z} {s} abs ⊢P ⊢t ⊢z ⊢s =
    IndRectⱼ abs nat∈ ⊢P ⊢t
      (PE.subst (λ As → Γ ⊢All (z TL.∷ s TL.∷ TL.[]) ∷ As ^ [ rG , ι lG ])
        (PE.sym (indRectBranchTyList-nat P rG lG))
        (consⱼ ⊢z (consⱼ ⊢s εⱼ)))
