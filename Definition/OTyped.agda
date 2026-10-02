{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
module Definition.OTyped (senv : SI.SEnv) where
open import Definition.OUntyped senv
open import Tools.Nat using (Nat; 1+; _+_; _-_; plusZero; plusSuc; plus-comm; _<<_; _≟_; leS; le0; le-refl; le-plus-left; minus-suc)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary using (yes; no)
open import Tools.List using (List; map; foldr; length; range; length-map; range-suc; zip; _∷ʳ_; replicate; replicate-snoc; length-replicate; zip-range-cons; _∈ₗ_; hereₗ; thereₗ; ∈ₗ-map-1+; ∈ₗ-range; ∈ₗ-map-inv; zip-∈ₗ)
open import Tools.Maybe using (just)
open import Tools.Inequality using (Bool; true; false; eqb; filter; filter-map; if_then_else_; filter-∈ₗ)
import Tools.List as TL
import Tools.PropositionalEquality as PE
open import Definition.Sort
import Definition.SUntyped as SU
import Definition.STyped senv as ST

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
           → Γ ⊢All args ∷ map emb-stype-oterm Ts ^ [ ! , ι ⁰ ]
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
    cast-Ind-refl : ∀ {ind e t}
               → ind ∈ₗ senv
               → Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ]
               → Γ ⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e t
                   ≡ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
    
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

    cast-Ind-refl : ∀ {ind e t}
            → ind ∈ₗ senv
            → Γ ⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ]
            → Γ ⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
            → Γ ⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e t
                ⇒ t ∷ Ind (SU.SInd.name ind) ^ ι ⁰


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

emb-stype-oterm-has-type : ∀ (A : SU.Type) {Γ} → SU.indsInSEnv senv A → ⊢ Γ → Γ ⊢ emb-stype-oterm A ∷ U ⁰ ^ [ ! , next ⁰ ]
emb-stype-oterm-has-type (SU.Ind n) n∈ ⊢Γ with ∈ₗ-map-inv SU.SInd.name senv n n∈
... | ind , PE.refl , ind∈ = Indⱼ ⊢Γ ind∈
emb-stype-oterm-has-type (SU.Arrow A B) (A∈ , B∈) ⊢Γ =
  Πⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) ▹ (λ ()) ▹ (emb-stype-oterm-has-type A A∈ ⊢Γ)
     ▹ (emb-stype-oterm-has-type B B∈ (⊢Γ ∙ univ (emb-stype-oterm-has-type A A∈ ⊢Γ)))

-- Embedded simple types are closed
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

-- A simple context embedded on top of an observational context
_∙ˢ_ : Con Term → ST.Con → Con Term
Γ ∙ˢ TL.[] = Γ
Γ ∙ˢ (A TL.∷ Δ) = (Γ ∙ˢ Δ) ∙ emb-stype-oterm A ^ [ ! , ι ⁰ ]

emb-scon : ST.Con → Con Term
emb-scon Δ = ε ∙ˢ Δ

Π⁰ : Term → Term → Term
Π⁰ A B = Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !

-- The types of simple terms in a declared context are declared
st-var-inds : ∀ {x A Γ} → TL.All (SU.indsInSEnv senv) Γ → x ST.∷ A ∈ Γ → SU.indsInSEnv senv A
st-var-inds (A∈ TL.∷ₐ _) ST.here = A∈
st-var-inds (_ TL.∷ₐ Γ∈) (ST.there h) = st-var-inds Γ∈ h

st-type-inds : ∀ {Γ t A} → TL.All (SU.indsInSEnv senv) Γ → Γ ST.⊢ t ∷ A → SU.indsInSEnv senv A
st-type-inds Γ∈ (ST.varⱼ h) = st-var-inds Γ∈ h
st-type-inds Γ∈ (ST.appⱼ f∈ _) = proj₂ (st-type-inds Γ∈ f∈)
st-type-inds Γ∈ (ST.lamⱼ A∈ t∈) = A∈ , st-type-inds (A∈ TL.∷ₐ Γ∈) t∈
st-type-inds Γ∈ (ST.ctrⱼ ind∈ _ _ _) = TL.∈ₗ-map SU.SInd.name ind∈
st-type-inds Γ∈ (ST.indRectⱼ _ P∈ _ _) = P∈

length-ctrRecIndices : ∀ i Ss →
  length (ctrRecIndices i Ss) PE.≡ SU.recCountList i Ss
length-ctrRecIndices i Ss =
  let as = Ss
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

method≡branch : ∀ ind P j Ss → ind ∈ₗ senv → SU.ctrArgsTypeList ind j PE.≡ just Ss →
  emb-stype-oterm (SU.indRectBranchTy (SU.SInd.name ind) Ss P)
    PE.≡ indRectBranchTy (SU.SInd.name ind) j Ss (wk1 (emb-stype-oterm P)) ! ⁰
method≡branch ind P j Ss ind∈ ctr≡ = eq
  where
  as = Ss
  Pemb = emb-stype-oterm P
  n = length (ctrArgsTypeList Ss)
  recs = ctrRecIndices (SU.SInd.name ind) Ss
  k = length recs
  concR = wk1 Pemb [ ctr (SU.SInd.name ind) j (map (λ j → var (((k + n) - 1) - j)) (range n)) ]↑^ (k + n)
  ihFun : Nat × Nat → Term
  ihFun pj = wk1 Pemb [ var (((n - 1) - proj₁ pj) + proj₂ pj) ]↑^ (n + proj₂ pj)
  ihTys = map ihFun (zip recs (range k))
  innerL = foldr Π⁰ Pemb (replicate k Pemb)
  innerR = foldr Π⁰ concR ihTys
  rhs≡ : indRectBranchTy (SU.SInd.name ind) j Ss (wk1 Pemb) ! ⁰ PE.≡ foldr Π⁰ innerR (map emb-stype-oterm as)
  rhs≡ = PE.cong (foldr Π⁰ innerR)
           (map-map proj₁ (λ T → (emb-stype-oterm T , 0)) (Ss))
  emb-indRectBranchTy-stype : ∀ i Ss P →
    emb-stype-oterm (SU.indRectBranchTy i Ss P) PE.≡
    foldr Π⁰ (foldr Π⁰ (emb-stype-oterm P)
                (replicate (SU.recCountList i Ss) (emb-stype-oterm P)))
      (map emb-stype-oterm Ss)
  emb-indRectBranchTy-stype i Ss P =
    PE.trans (emb-arrows Ts (SU.arrowRepeat k′ P P))
      (PE.cong (λ B → foldr Π⁰ B (map emb-stype-oterm Ts))
        (emb-arrowRepeat k′ P P))
    where
    Ts = Ss
    k′  = SU.recCountList i Ss
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
  -- The motive of the embedding is a weakening of a simple type, so every
  -- substitution performed by a method type leaves it unchanged.
  P↑-const : ∀ d u → wk1 Pemb [ u ]↑^ d PE.≡ Pemb
  P↑-const d u =
    PE.trans (PE.cong (λ t → t [ u ]↑^ d) (emb-stype-wk-id P (step id)))
      (emb-stype-subst-id P (consSubst (wk1^Subst d idSubst) u))
  inner≡ : innerL PE.≡ innerR
  inner≡ =
    PE.trans (PE.cong (λ m → foldr Π⁰ Pemb (replicate m Pemb)) (PE.sym lenzip))
      (go (zip recs (range k)))
    where
    lenzip : length (zip recs (range k)) PE.≡ k
    lenzip = TL.length-zip-eq recs (range k) (PE.sym (TL.length-range k))
    go : ∀ xs → foldr Π⁰ Pemb (replicate (length xs) Pemb)
                  PE.≡ foldr Π⁰ concR (map ihFun xs)
    go TL.[] =
      PE.sym (P↑-const (k + n)
               (ctr (SU.SInd.name ind) j (map (λ j → var (((k + n) - 1) - j)) (range n))))
    go (x TL.∷ xs) =
      PE.cong₂ Π⁰
        (PE.sym (P↑-const (n + proj₂ x) (var (((n - 1) - proj₁ x) + proj₂ x))))
        (go xs)
  eq : emb-stype-oterm (SU.indRectBranchTy (SU.SInd.name ind) Ss P) PE.≡
       indRectBranchTy (SU.SInd.name ind) j Ss (wk1 Pemb) ! ⁰
  eq = PE.trans (emb-indRectBranchTy-stype (SU.SInd.name ind) Ss P)
         (PE.trans
           (PE.cong (λ m → foldr Π⁰ (foldr Π⁰ Pemb (replicate m Pemb))
                             (map emb-stype-oterm as))
             (PE.sym (length-ctrRecIndices (SU.SInd.name ind) Ss)))
           (PE.trans (PE.cong (λ B → foldr Π⁰ B (map emb-stype-oterm as)) inner≡)
             (PE.sym rhs≡)))

emb-indRectBranchTyList-stype : ∀ ind P → ind ∈ₗ senv →
  map emb-stype-oterm (SU.indRectBranchTypeList ind P)
    PE.≡ indRectBranchTyList ind (wk1 (emb-stype-oterm P)) ! ⁰
emb-indRectBranchTyList-stype ind P ind∈ =
  PE.trans
    (PE.trans
      (map-map emb-stype-oterm (λ Ts → SU.indRectBranchTy (SU.SInd.name ind) Ts P) Tss)
      (TL.map-zip-range (λ Ts → emb-stype-oterm (SU.indRectBranchTy (SU.SInd.name ind) Ts P)) Tss))
    (map-≡ ctrs
      (λ jTs jTs∈ → method≡branch ind P (proj₁ jTs) (proj₂ jTs) ind∈
                      (TL.zip-range-nth Tss jTs jTs∈)))
  where
  Tss = SU.SInd.ctrArgsTypes ind
  ctrs = zip (range (SU.indCtrCount ind)) Tss
  map-≡ : ∀ {A : Set} {f g : A → Term} ns →
    (∀ j → j TL.∈ₗ ns → f j PE.≡ g j) →
    map f ns PE.≡ map g ns
  map-≡ TL.[] _ = PE.refl
  map-≡ (n TL.∷ ns) h =
    PE.cong₂ TL._∷_ (h n TL.hereₗ) (map-≡ ns (λ j j∈ → h j (TL.thereₗ j∈)))

-- Simple terms typed in [Δ] are typed in any well-formed context extended by [Δ]
emb-sterm-oterm-preserves-typing′ : ∀ {Γ Δ t A} → ⊢ Γ
  → TL.All (SU.indsInSEnv senv) Δ
  → Δ ST.⊢ t ∷ A
  → (Γ ∙ˢ Δ) ⊢ emb-sterm-oterm t ∷ emb-stype-oterm A ^ [ ! , ι ⁰ ]
emb-sterm-oterm-preserves-typing′ {Γ₀} ⊢Γ₀ = go
  where
  emb-scon-wf : ∀ Γ → TL.All (SU.indsInSEnv senv) Γ → ⊢ (Γ₀ ∙ˢ Γ)
  emb-scon-wf TL.[] TL.[]ₐ = ⊢Γ₀
  emb-scon-wf (A TL.∷ Γ) (A∈ TL.∷ₐ Γ∈) = emb-scon-wf Γ Γ∈ ∙ univ (emb-stype-oterm-has-type A A∈ (emb-scon-wf Γ Γ∈))

  emb-stype-wk1n-id : ∀ A n → repeat wk1 (emb-stype-oterm A) n PE.≡ emb-stype-oterm A
  emb-stype-wk1n-id A 0 = PE.refl
  emb-stype-wk1n-id A (1+ n) =
    PE.trans (PE.cong wk1 (emb-stype-wk1n-id A n)) (emb-stype-wk-id A (step id))

  emb-st-var-wk-depth : ∀ {x A Γ} → x ST.∷ A ∈ Γ → Nat
  emb-st-var-wk-depth ST.here = 1
  emb-st-var-wk-depth (ST.there h) = 1+ (emb-st-var-wk-depth h)

  emb-st-var∈ : ∀ {x A Γ} (h : x ST.∷ A ∈ Γ)
    → x ∷ repeat wk1 (emb-stype-oterm A) (emb-st-var-wk-depth h) ^ [ ! , ι ⁰ ] ∈ (Γ₀ ∙ˢ Γ)
  emb-st-var∈ ST.here = here
  emb-st-var∈ (ST.there h) = there (emb-st-var∈ h)

  emb-st-wkTy≡ : ∀ {Γ A} d → SU.indsInSEnv senv A → ⊢ ((Γ₀ ∙ˢ Γ))
    → (Γ₀ ∙ˢ Γ) ⊢ repeat wk1 (emb-stype-oterm A) d ≡ emb-stype-oterm A ^ [ ! , ι ⁰ ]
  emb-st-wkTy≡ {Γ} {A} d A∈ ⊢Γ =
    PE.subst (λ (embTy : Term) → (Γ₀ ∙ˢ Γ) ⊢ repeat wk1 (emb-stype-oterm A) d ≡ embTy ^ [ ! , ι ⁰ ])
            (emb-stype-wk1n-id A d)
            (refl (PE.subst (λ (embTy : Term) → (Γ₀ ∙ˢ Γ) ⊢ embTy ^ [ ! , ι ⁰ ])
                           (PE.sym (emb-stype-wk1n-id A d))
                           (univ (emb-stype-oterm-has-type A A∈ ⊢Γ))))

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

  mutual
    go-all : ∀ {Γ args As}
      → TL.All (SU.indsInSEnv senv) Γ
      → Γ ST.⊢All args ∷ As
      → (Γ₀ ∙ˢ Γ) ⊢All (emb-sterm-oterm-all args) ∷ map emb-stype-oterm As ^ [ ! , ι ⁰ ]
    go-all Γ∈ ST.εⱼ = εⱼ
    go-all Γ∈ (ST.consⱼ t∈ ts∈) = consⱼ (go Γ∈ t∈) (go-all Γ∈ ts∈)

    go : ∀ {Γ t A}
      → TL.All (SU.indsInSEnv senv) Γ
      → Γ ST.⊢ t ∷ A
      → (Γ₀ ∙ˢ Γ) ⊢ emb-sterm-oterm t ∷ emb-stype-oterm A ^ [ ! , ι ⁰ ]
    go Γ∈ (ST.varⱼ h) =
      conv (var (emb-scon-wf _ Γ∈) (emb-st-var∈ h))
           (emb-st-wkTy≡ (emb-st-var-wk-depth h) (st-var-inds Γ∈ h) (emb-scon-wf _ Γ∈))
    go Γ∈ (ST.appⱼ {A = A} {B = B} f∈ a∈) =
      let A∈ , B∈ = st-type-inds Γ∈ f∈ in
      conv (_▹_▹_▹_∘ⱼ_ {F = emb-stype-oterm A} {G = emb-stype-oterm B}
              {lG = ⁰} {r = !} {lΠ = ⁰}
              (λ ())
              (emb-stype-oterm-has-type A A∈ (emb-scon-wf _ Γ∈))
              (emb-stype-oterm-has-type B B∈ (emb-scon-wf _ Γ∈ ∙ univ (emb-stype-oterm-has-type A A∈ (emb-scon-wf _ Γ∈))))
              (go Γ∈ f∈)
              (go Γ∈ a∈))
           (PE.subst (λ (embTy : Term) → (Γ₀ ∙ˢ _) ⊢ emb-stype-oterm B [ emb-sterm-oterm _ ] ≡ embTy ^ [ ! , ι ⁰ ])
                     (emb-stype-subst-id B (sgSubst (emb-sterm-oterm _)))
                     (refl (PE.subst (λ (embTy : Term) → (Γ₀ ∙ˢ _) ⊢ embTy ^ [ ! , ι ⁰ ])
                                    (PE.sym (emb-stype-subst-id B (sgSubst (emb-sterm-oterm _))))
                                    (univ (emb-stype-oterm-has-type B B∈ (emb-scon-wf _ Γ∈))))))
    go Γ∈ (ST.lamⱼ {A = A} A∈ t∈) =
      lamⱼ (λ _ → ⁰min ⁰ , ⁰min ⁰) (λ ())
        (univ (emb-stype-oterm-has-type A A∈ (emb-scon-wf _ Γ∈)))
        (go (A∈ TL.∷ₐ Γ∈) t∈)
    go Γ∈ (ST.ctrⱼ {ind} {j} ind∈ eq _ args∈) =
      Ctrⱼ (emb-scon-wf _ Γ∈) ind∈ eq (go-all Γ∈ args∈)
    go {Γ} Γ∈ (ST.indRectⱼ {ind} {P} {t} {ms} ind∈ P∈ t∈ ms∈) =
      let ⊢Γ = emb-scon-wf Γ Γ∈
          ⊢Ind = univ (Indⱼ ⊢Γ ind∈)
          ⊢ΓInd = ⊢Γ ∙ ⊢Ind
          Pemb = emb-stype-oterm P
          ⊢Pemb∙ = emb-stype-oterm-has-type P P∈ ⊢ΓInd
          ⊢wk1Pemb =
            PE.subst (λ u → (Γ₀ ∙ˢ Γ) ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ u ∷ U ⁰ ^ [ ! , next ⁰ ])
              (PE.sym (emb-stype-wk-id P (step id)))
              ⊢Pemb∙
          ⊢t = go Γ∈ t∈
          ⊢ms = PE.subst (λ As → (Γ₀ ∙ˢ Γ) ⊢All emb-sterm-oterm-all ms ∷ As ^ [ ! , ι ⁰ ])
                  (emb-indRectBranchTyList-stype ind P ind∈) (go-all Γ∈ ms∈)
          ⊢elim = IndRectⱼ (λ ()) ind∈ (univ ⊢wk1Pemb) ⊢t ⊢ms
          Pty≡ = PE.trans (PE.cong (λ u → u [ emb-sterm-oterm t ]) (emb-stype-wk-id P (step id)))
                   (emb-stype-subst-id P (sgSubst (emb-sterm-oterm t)))
          Pty≡ty = PE.subst (λ T → (Γ₀ ∙ˢ Γ) ⊢ T ≡ Pemb ^ [ ! , ι ⁰ ])
                     (PE.sym Pty≡)
                     (refl (univ (emb-stype-oterm-has-type P P∈ ⊢Γ)))
      in  conv ⊢elim Pty≡ty

emb-sterm-oterm-preserves-typing : ∀ {Γ t A}
  → TL.All (SU.indsInSEnv senv) Γ
  → Γ ST.⊢ t ∷ A
  → emb-scon Γ ⊢ emb-sterm-oterm t ∷ emb-stype-oterm A ^ [ ! , ι ⁰ ]
emb-sterm-oterm-preserves-typing = emb-sterm-oterm-preserves-typing′ ε
