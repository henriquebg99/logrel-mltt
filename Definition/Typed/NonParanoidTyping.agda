{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.NonParanoidTyping (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs as T hiding (wf ; wfTerm)
open import Definition.Typed.Weakening senv equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty
open import Tools.List using (List; map; All₃; nth; _++_; _∈ₗ_; []ₐ; _∷ₐ_)
import Tools.List as TL
open import Tools.Maybe using (just)
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU
import Definition.Equiv senv as Eq
infixl 30 _∙_
infix 30 Πⱼ_▹_▹_

mutual
  -- Well-formed context
  data ⊢⊢_ : Con Term → Set where
    ε   : ⊢⊢ ε
    _∙_ : ∀ {Γ A r}
        → ⊢⊢ Γ
        → Γ ⊢⊢ A ^ r
        → ⊢⊢ Γ ∙ A ^ r

  -- Well-formed type
  data _⊢⊢_^_ (Γ : Con Term) : Term → TypeInfo → Set where
    Uⱼ    : ∀ {r} → ⊢⊢ Γ → Γ ⊢⊢ Univ r ¹ ^ [ ! , ∞ ]
    univ : ∀ {A r l}
         → Γ ⊢⊢ A ∷ Univ r l ^ [ ! , next l ]
         → Γ ⊢⊢ A ^ [ r , ι l ]

  -- Well-formed term of a type
  data _⊢⊢_∷_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ : ∀ {r l l'}
         → l < l'
         → ⊢⊢ Γ
         → Γ ⊢⊢ (Univ r l) ∷ (Univ ! l') ^ [ ! , next l' ]
    Indⱼ    : ∀ {ind} → ⊢⊢ Γ → ind ∈ₗ senv → Γ ⊢⊢ Ind (SU.SInd.name ind) ∷ U ⁰ ^ [ ! , ι ¹ ]
    Emptyⱼ : ⊢⊢ Γ → Γ ⊢⊢ sEmpty ∷ SProp ^ [ ! , ι ¹ ]
    Πⱼ_▹_▹_ : ∀ {F rF lF G lG r l}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G ^ [ r , ι lG ]
           → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ∷ (Univ r l) ^ [ ! , next l ]
    var    : ∀ {A rl x}
           → ⊢⊢ Γ
           → x ∷ A ^ rl ∈ Γ
           → Γ ⊢⊢ var x ∷ A ^ rl
    lamⱼ    : ∀ {F r l rF lF G lG t}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ t ∷ G ^ [ r , ι lG ]
           → Γ     ⊢⊢ lam F ▹ t ^ l ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ^ [ r , ι l ]
    _∘ⱼ_    : ∀ {g a F rF lF G lG r lΠ}
           → Γ ⊢⊢     g ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r ^ [ r , ι lΠ ]
           → Γ ⊢⊢     a ∷ F ^ [ rF , ι lF ]
           → Γ ⊢⊢ g ∘ a ^ lΠ ∷ G [ a ] ^ [ r , ι lG ]
    fstⱼ : ∀ {A A' rA B B' e}
           → Γ ⊢⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ]
           → Γ ⊢⊢ fst e ∷ Id (Univ rA ⁰) A A' ^ [ % , ι ⁰ ]
    sndⱼ : ∀ {A A' rA B B' e}
           → Γ ⊢⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ]
           → Γ ⊢⊢ snd e ∷ Π A' ^ rA ° ⁰ ▹ Id (U ⁰)
                        (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                        B' ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
    Ctrⱼ    : ∀ {ind j args Ts}
           → ⊢⊢ Γ
           → ind ∈ₗ senv
           → SU.ctrArgsTypeList ind j PE.≡ just Ts
           → Γ ⊢⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
           → Γ ⊢⊢ ctr (SU.SInd.name ind) j args ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
    IndRectⱼ : ∀ {ind P rG lG t ms}
           → (rG PE.≡ % → lG PE.≡ ⁰)
           → ind ∈ₗ senv
           → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢⊢ P ^ [ rG , ι lG ]
           → Γ ⊢⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
           → Γ ⊢⊢All ms ∷ indRectBranchTyList ind P rG lG ^ [ rG , ι lG ]
           → Γ ⊢⊢ IndRect (SU.SInd.name ind) lG P t ms ∷ P [ t ] ^ [ rG , ι lG ]
    Emptyrecⱼ : ∀ {A lA rA e}
           → Γ ⊢⊢ A ^ [ rA , ι lA ] → Γ ⊢⊢ e ∷ sEmpty ^ [ % ,  ι ⁰ ] -> Γ ⊢⊢ Emptyrec lA ⁰ A e ∷ A ^ [ rA , ι lA ]
    Idⱼ : ∀ {A l t u}
          → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
          → Γ ⊢⊢ u ∷ A ^ [ ! , ι l ]
          → Γ ⊢⊢ Id A t u ∷ SProp ^ [ ! , next ⁰ ]
    Idreflⱼ : ∀ {A l t}
              → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ Idrefl A t ∷ (Id A t t) ^ [ % , ι ⁰ ]
    transpⱼ : ∀ {A l P t s u e}
              → Γ ∙ A ^ [ ! , l ] ⊢⊢ P ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ t ∷ A ^ [ ! , l ]
              → Γ ⊢⊢ s ∷ P [ t ] ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ u ∷ A ^ [ ! , l ]
              → Γ ⊢⊢ e ∷ (Id A t u) ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ transp A P t s u e ∷ P [ u ] ^ [ % , ι ⁰ ]
    castⱼ : ∀ {A B r e t}
            → Γ ⊢⊢ e ∷ (Id (Univ r ⁰) A B) ^ [ % , ι ⁰ ]
            → Γ ⊢⊢ t ∷ A ^ [ r , ι ⁰ ]
            → Γ ⊢⊢ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ]
    conv   : ∀ {t A B r}
           → Γ ⊢⊢ t ∷ A ^ r
           → Γ ⊢⊢ A ≡ B ^ r
           → Γ ⊢⊢ t ∷ B ^ r
    equiv-eqⱼ : ∀ {n e}
              → ⊢⊢ Γ
              → (nth equivs n PE.≡ just e)
              → Γ ⊢⊢ equiv-eq n ∷ Id (U ⁰) (Ind (E.Equiv.indA e)) (Ind (E.Equiv.indB e)) ^ [ % , ι ⁰ ]

  -- Pointwise typing of lists of terms
  data _⊢⊢All_∷_^_ (Γ : Con Term) : List Term → List Term → TypeInfo → Set where
    εⱼ   : ∀ {r} → Γ ⊢⊢All TL.[] ∷ TL.[] ^ r
    consⱼ  : ∀ {t ts A As r}
         → Γ ⊢⊢ t ∷ A ^ r
         → Γ ⊢⊢All ts ∷ As ^ r
         → Γ ⊢⊢All (t TL.∷ ts) ∷ (A TL.∷ As) ^ r

  -- Pointwise conversion of lists of terms
  data _⊢⊢All_≡_∷_^_ (Γ : Con Term) : List Term → List Term → List Term → TypeInfo → Set where
    εⱼ   : ∀ {r} → Γ ⊢⊢All TL.[] ≡ TL.[] ∷ TL.[] ^ r
    consⱼ  : ∀ {t t′ ts ts′ A As r}
         → Γ ⊢⊢ t ≡ t′ ∷ A ^ r
         → Γ ⊢⊢All ts ≡ ts′ ∷ As ^ r
         → Γ ⊢⊢All (t TL.∷ ts) ≡ (t′ TL.∷ ts′) ∷ (A TL.∷ As) ^ r

  -- Type equality
  data _⊢⊢_≡_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ   : ∀ {A B r l}
           → Γ ⊢⊢ A ≡ B ∷ (Univ r l) ^ [ ! , next l ]
           → Γ ⊢⊢ A ≡ B ^ [ r , ι l ]
    refl   : ∀ {A r}
           → Γ ⊢⊢ A ^ r
           → Γ ⊢⊢ A ≡ A ^ r
    sym    : ∀ {A B r}
           → Γ ⊢⊢ A ≡ B ^ r
           → Γ ⊢⊢ B ≡ A ^ r
    trans  : ∀ {A B C r}
           → Γ ⊢⊢ A ≡ B ^ r
           → Γ ⊢⊢ B ≡ C ^ r
           → Γ ⊢⊢ A ≡ C ^ r


  -- Term equality
  data _⊢⊢_≡_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeInfo → Set where
    refl        : ∀ {t A l}
                → Γ ⊢⊢ t ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ t ≡ t ∷ A ^ [ ! , l ]
    sym         : ∀ {t u A l}
                → Γ ⊢⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ u ≡ t ∷ A ^ [ ! , l ]
    trans       : ∀ {t u v A l}
                → Γ ⊢⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ u ≡ v ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ t ≡ v ∷ A ^ [ ! , l ]
    conv        : ∀ {A B r t u}
                → Γ ⊢⊢ t ≡ u ∷ A ^ r
                → Γ ⊢⊢ A ≡ B ^ r
                → Γ ⊢⊢ t ≡ u ∷ B ^ r
    Π-cong      : ∀ {E F G H rF lF rG lG l}
                → (rG PE.≡ ! → lF ≤ l × lG ≤ l)
                → (rG PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
                → Γ     ⊢⊢ F ≡ H ^ [ rF , ι lF ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G ≡ E ^ [ rG , ι lG ]
                → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ rG ≡ Π H ^ rF ° lF ▹ E ° lG ° l ^ rG ∷ (Univ rG l) ^ [ ! , next l ]
    app-cong    : ∀ {a b f g F G rF lF lG l}
                → Γ ⊢⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ ⊢⊢ a ≡ b ∷ F ^ [ rF , ι lF ]
                → Γ ⊢⊢ f ∘ a ^ l ≡ g ∘ b ^ l ∷ G [ a ] ^ [ ! , ι lG ]
    β-red       : ∀ {a t F rF lF G lG l}
                → lF ≤ l
                → lG ≤ l
                → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ t ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢⊢ a ∷ F ^ [ rF , ι lF ]
                → Γ     ⊢⊢ (lam F ▹ t ^ l) ∘ a ^ l ≡ t [ a ] ∷ G [ a ] ^ [ ! , ι lG ]
    η-eq        : ∀ {f g F rF lF lG l G}
                → Γ     ⊢⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ wk1 f ∘ var Nat.zero ^ l ≡ wk1 g ∘ var Nat.zero ^ l ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
    ctr-cong    : ∀ {ind j args args' Ts}
                → ⊢⊢ Γ
                → ind ∈ₗ senv
                → SU.ctrArgsTypeList ind j PE.≡ just Ts
                → All₃ (λ a a' A → Γ ⊢⊢ a ≡ a' ∷ A ^ [ ! , ι ⁰ ]) args args' (map emb-stype Ts)
                → Γ ⊢⊢ ctr (SU.SInd.name ind) j args ≡ ctr (SU.SInd.name ind) j args' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
    IndRect-cong : ∀ {ind P P' lG t t' ms ms'}
                → ind ∈ₗ senv
                → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢⊢ P ≡ P' ^ [ ! , ι lG ]
                → Γ ⊢⊢ t ≡ t' ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
                → Γ ⊢⊢All ms ≡ ms' ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
                → Γ ⊢⊢ IndRect (SU.SInd.name ind) lG P t ms ≡ IndRect (SU.SInd.name ind) lG P' t' ms' ∷ P [ t ] ^ [ ! , ι lG ]
    IndRect-ctr≡ : ∀ {ind j P lG args ms m Ts}
                → ind ∈ₗ senv
                → SU.ctrArgsTypeList ind j PE.≡ just Ts
                → Γ ∙ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢⊢ P ^ [ ! , ι lG ]
                → Γ ⊢⊢All args ∷ map emb-stype Ts ^ [ ! , ι ⁰ ]
                → Γ ⊢⊢All ms ∷ indRectBranchTyList ind P ! lG ^ [ ! , ι lG ]
                → nth ms j PE.≡ just m
                → Γ ⊢⊢ IndRect (SU.SInd.name ind) lG P (ctr (SU.SInd.name ind) j args) ms
                    ≡ apps lG m
                             (args ++ map (λ a → IndRect (SU.SInd.name ind) lG P a ms)
                                     (ctrRecArgs (SU.SInd.name ind) Ts args))
                    ∷ P [ ctr (SU.SInd.name ind) j args ] ^ [ ! , ι lG ]
    Emptyrec-cong : ∀ {A A' l e e'}
                → Γ ⊢⊢ A ≡ A' ^ [ ! , ι l ]
                → Γ ⊢⊢ e ∷ sEmpty ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ e' ∷ sEmpty ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ Emptyrec l ⁰  A e ≡ Emptyrec l ⁰  A' e' ∷ A ^ [ ! , ι l ]
    proof-irrelevance : ∀ {t u A l}
                      → Γ ⊢⊢ t ∷ A ^ [ % , l ]
                      → Γ ⊢⊢ u ∷ A ^ [ % , l ]
                      → Γ ⊢⊢ t ≡ u ∷ A ^ [ % , l ]
    Id-cong : ∀ {A A' l t t' u u'}
              → Γ ⊢⊢ A ≡ A' ^ [ ! , ι l ]
              → Γ ⊢⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ u ≡ u' ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ Id A t u ≡ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ]
    cast-refl : ∀ {A B e t} → let l = ⁰ in
                  Γ ⊢⊢ A ≡ B ^ [ ! , ι l ]
                → Γ ⊢⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
                → Γ ⊢⊢ cast l A B e t ≡ t ∷ B ^ [ ! , ι l ]            
    cast-cong : ∀ {A A' B B' e e' t t'} → let l = ⁰ in
                  Γ ⊢⊢ A ≡ A' ^ [ ! , ι l ]
                → Γ ⊢⊢ B ≡ B' ^ [ ! , ι l ]
                → Γ ⊢⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
                → Γ ⊢⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ cast l A B e t ≡ cast l A' B' e' t' ∷ B ^ [ ! , ι l ]
    cast-Π : ∀ {A A' rA B B' e f} → let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
               Γ ⊢⊢ e ∷ Id (U l) (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) ^ [ % , ι l ]
             → Γ ⊢⊢ f ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) ^ [ ! , ι l ]
             → Γ ⊢⊢ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f)
               ≡ (lam A' ▹
                      (let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                      cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ l))
                      ^ l)
                   ∷ Π A' ^ rA ° lA ▹ B' ° lB ° l  ^ ! ^ [ ! , ι l ]
    cast-equiv : ∀ {A B e t}
               → (A∈ : A ∈ₗ SU.indNames senv)
               → (B∈ : B ∈ₗ SU.indNames senv)
               → A PE.≢ B
               → (H : reprInd A PE.≡ reprInd B)
               → Γ ⊢⊢ e ∷ Id (U ⁰) (Ind A) (Ind B) ^ [ % , ι ⁰ ]
               → Γ ⊢⊢ t ∷ Ind A ^ [ ! , ι ⁰ ]
               → Γ ⊢⊢ cast ⁰ (Ind A) (Ind B) e t
                   ≡ emb-oterm (Eq.fwdₒ (Eq.repr-equiv equivs A B A∈ B∈ H)) ∘ t ^ ⁰
                   ∷ Ind B ^ [ ! , ι ⁰ ]

mutual 
  wfTerm : ∀ {Γ A t r} → Γ ⊢⊢ t ∷ A ^ r → ⊢⊢ Γ
  wfTerm (univ <l ⊢⊢Γ) = ⊢⊢Γ
  wfTerm (Indⱼ ⊢⊢Γ _) = ⊢⊢Γ
  wfTerm (Emptyⱼ ⊢⊢Γ) = ⊢⊢Γ
  wfTerm (Πⱼ <l ▹ <l' ▹ G) with wf G
  ... | ⊢Γ ∙ F = ⊢Γ
  wfTerm (var ⊢⊢Γ x₁) = ⊢⊢Γ
  wfTerm (lamⱼ _ _ t) with wfTerm t
  wfTerm (lamⱼ _ _ t) | ⊢⊢Γ ∙ F′ = ⊢⊢Γ
  wfTerm (g ∘ⱼ a) = wfTerm a
  wfTerm (fstⱼ e) = wfTerm e
  wfTerm (sndⱼ e) = wfTerm e
  wfTerm (Ctrⱼ ⊢⊢Γ _ _ _) = ⊢⊢Γ
  wfTerm (IndRectⱼ _ _ P t ms) = wfTerm t
  wfTerm (Emptyrecⱼ A e) = wfTerm e
  wfTerm (Idⱼ t u) = wfTerm t
  wfTerm (Idreflⱼ t) = wfTerm t
  wfTerm (transpⱼ P t s u e) = wfTerm t
  wfTerm (castⱼ e t) = wfTerm t
  wfTerm (conv t A≡B) = wfTerm t
  wfTerm (equiv-eqⱼ ⊢⊢Γ _) = ⊢⊢Γ

  wf : ∀ {Γ A r} → Γ ⊢⊢ A ^ r → ⊢⊢ Γ
  wf (Uⱼ ⊢⊢Γ) = ⊢⊢Γ
  wf (univ A) = wfTerm A

adm-cast-Ind-refl : ∀ {Γ ind e t}
         → ind ∈ₗ senv
         → Γ ⊢⊢ e ∷ Id (U ⁰) (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) ^ [ % , ι ⁰ ]
         → Γ ⊢⊢ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
         → Γ ⊢⊢ cast ⁰ (Ind (SU.SInd.name ind)) (Ind (SU.SInd.name ind)) e t ≡ t ∷ Ind (SU.SInd.name ind) ^ [ ! , ι ⁰ ]
adm-cast-Ind-refl ind∈ ⊢⊢e ⊢⊢t = let ⊢⊢Γ = wfTerm ⊢⊢e
                                in cast-refl (refl (univ (Indⱼ ⊢⊢Γ ind∈))) ⊢⊢e ⊢⊢t


mutual
  ⊢is⊢⊢ctx : ∀ {Γ} → ⊢ Γ → ⊢⊢ Γ
  ⊢is⊢⊢ : ∀ {Γ A r} → Γ ⊢ A ^ r → Γ ⊢⊢ A ^ r
  ⊢is⊢⊢eq : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → Γ ⊢⊢ A ≡ B ^ r
  ⊢is⊢⊢term : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → Γ ⊢⊢ t ∷ A ^ r
  ⊢is⊢⊢eqterm : ∀ {Γ A t u r} → Γ ⊢ t ≡ u ∷ A ^ r → Γ ⊢⊢ t ≡ u ∷ A ^ r
  ⊢is⊢⊢All : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → Γ ⊢⊢All ts ∷ As ^ r
  ⊢is⊢⊢All≡ : ∀ {Γ ts us As r} → Γ ⊢All ts ≡ us ∷ As ^ r → Γ ⊢⊢All ts ≡ us ∷ As ^ r
  ⊢is⊢⊢All₃ : ∀ {Γ ts us As r} → All₃ (λ t u A → Γ ⊢ t ≡ u ∷ A ^ r) ts us As
            → All₃ (λ t u A → Γ ⊢⊢ t ≡ u ∷ A ^ r) ts us As
  
  ⊢is⊢⊢ctx ε = ε
  ⊢is⊢⊢ctx (⊢Γ ∙ x) = ⊢is⊢⊢ctx ⊢Γ ∙ ⊢is⊢⊢ x
  
  ⊢is⊢⊢ (Uⱼ x) = Uⱼ (⊢is⊢⊢ctx x)
  ⊢is⊢⊢ (univ x) = univ (⊢is⊢⊢term x)
  
  ⊢is⊢⊢eq (univ x) = univ (⊢is⊢⊢eqterm x)
  ⊢is⊢⊢eq (refl x) = refl (⊢is⊢⊢ x)
  ⊢is⊢⊢eq (sym X) = sym (⊢is⊢⊢eq X)
  ⊢is⊢⊢eq (trans X X₁) = trans (⊢is⊢⊢eq X) (⊢is⊢⊢eq X₁)
  
  ⊢is⊢⊢term (univ x ⊢Γ) = univ x (⊢is⊢⊢ctx ⊢Γ)
  ⊢is⊢⊢term (Indⱼ ⊢Γ ind∈) = Indⱼ (⊢is⊢⊢ctx ⊢Γ) ind∈
  ⊢is⊢⊢term (Emptyⱼ ⊢Γ) = Emptyⱼ (⊢is⊢⊢ctx ⊢Γ)
  ⊢is⊢⊢term (Πⱼ x ▹ x₁ ▹ X ▹ X₁) = Πⱼ x ▹ x₁ ▹ univ (⊢is⊢⊢term X₁)
  ⊢is⊢⊢term (var ⊢Γ x) = var (⊢is⊢⊢ctx ⊢Γ) x
  ⊢is⊢⊢term (lamⱼ x x₁ x₂ X) = lamⱼ x x₁ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (x ▹ X ▹ X₁ ▹ X₂ ∘ⱼ X₃) = ⊢is⊢⊢term X₂ ∘ⱼ ⊢is⊢⊢term X₃
  ⊢is⊢⊢term (fstⱼ X X₁ _ _ X₂) = fstⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (sndⱼ X X₁ _ _ X₂) = sndⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (Ctrⱼ ⊢Γ ind∈ eq X) = Ctrⱼ (⊢is⊢⊢ctx ⊢Γ) ind∈ eq (⊢is⊢⊢All X)
  ⊢is⊢⊢term (IndRectⱼ x ind∈ X X₁ X₂) = IndRectⱼ x ind∈ (⊢is⊢⊢ X) (⊢is⊢⊢term X₁) (⊢is⊢⊢All X₂)
  ⊢is⊢⊢term (Emptyrecⱼ x X) = Emptyrecⱼ (⊢is⊢⊢ x) (⊢is⊢⊢term X)
  ⊢is⊢⊢term (Idⱼ X X₁ X₂) = Idⱼ (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) 
  ⊢is⊢⊢term (Idreflⱼ X) = Idreflⱼ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (transpⱼ x x₁ X X₁ X₂ X₃) = transpⱼ (⊢is⊢⊢ x₁) (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃)
  ⊢is⊢⊢term (castⱼ X X₁ X₂ X₃) = castⱼ (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃) 
  ⊢is⊢⊢term (conv X x) = conv (⊢is⊢⊢term X) (⊢is⊢⊢eq x)
  ⊢is⊢⊢term (equiv-eqⱼ ⊢Γ x) = equiv-eqⱼ (⊢is⊢⊢ctx ⊢Γ) x

  ⊢is⊢⊢eqterm (refl x) = refl (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (sym X) = sym (⊢is⊢⊢eqterm X)
  ⊢is⊢⊢eqterm (trans X X₁) = trans (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (conv X x) = conv (⊢is⊢⊢eqterm X) (⊢is⊢⊢eq x)
  ⊢is⊢⊢eqterm (Π-cong x x₁ x₂ X X₁) = Π-cong x x₁ (univ (⊢is⊢⊢eqterm X)) (univ (⊢is⊢⊢eqterm X₁))
  ⊢is⊢⊢eqterm (app-cong X X₁) = app-cong (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (β-red x x₁ x₂ x₃ x₄) = β-red x x₁ (⊢is⊢⊢term x₃) (⊢is⊢⊢term x₄)
  ⊢is⊢⊢eqterm (η-eq x x₁ x₂ x₃ x₄ X) = η-eq (⊢is⊢⊢term x₃) (⊢is⊢⊢term x₄) (⊢is⊢⊢eqterm X)
  ⊢is⊢⊢eqterm (ctr-cong ⊢Γ ind∈ eq X) = ctr-cong (⊢is⊢⊢ctx ⊢Γ) ind∈ eq (⊢is⊢⊢All₃ X)
  ⊢is⊢⊢eqterm (IndRect-cong ind∈ x X X₁) = IndRect-cong ind∈ (⊢is⊢⊢eq x) (⊢is⊢⊢eqterm X) (⊢is⊢⊢All≡ X₁)
  ⊢is⊢⊢eqterm (IndRect-ctr≡ ind∈ eq x X X₁ nth≡) = IndRect-ctr≡ ind∈ eq (⊢is⊢⊢ x) (⊢is⊢⊢All X) (⊢is⊢⊢All X₁) nth≡
  ⊢is⊢⊢eqterm (Emptyrec-cong x x₁ x₂) = Emptyrec-cong (⊢is⊢⊢eq x) (⊢is⊢⊢term x₁) (⊢is⊢⊢term x₂)
  ⊢is⊢⊢eqterm (proof-irrelevance x x₁) = proof-irrelevance (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-cong X X₁ X₂) = Id-cong (univ (⊢is⊢⊢eqterm X)) (⊢is⊢⊢eqterm X₁) (⊢is⊢⊢eqterm X₂)
  ⊢is⊢⊢eqterm (cast-refl X x x₁) = cast-refl (univ (⊢is⊢⊢eqterm X)) (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (univ (⊢is⊢⊢eqterm X)) (univ (⊢is⊢⊢eqterm X₁)) (⊢is⊢⊢eqterm X₂) (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (cast-Π x x₁ x₂ x₃ x₄ x₅) = cast-Π (⊢is⊢⊢term x₄) (⊢is⊢⊢term x₅)
  ⊢is⊢⊢eqterm (cast-Ind-refl ind∈ x x₁) = adm-cast-Ind-refl ind∈ (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (cast-equiv A∈ B∈ A≢B H x x₁) = cast-equiv A∈ B∈ A≢B H (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)

  ⊢is⊢⊢All εⱼ = εⱼ
  ⊢is⊢⊢All (consⱼ x X) = consⱼ (⊢is⊢⊢term x) (⊢is⊢⊢All X)

  ⊢is⊢⊢All≡ εⱼ = εⱼ
  ⊢is⊢⊢All≡ (consⱼ x X) = consⱼ (⊢is⊢⊢eqterm x) (⊢is⊢⊢All≡ X)

  ⊢is⊢⊢All₃ []ₐ = []ₐ
  ⊢is⊢⊢All₃ (x ∷ₐ X) = ⊢is⊢⊢eqterm x ∷ₐ ⊢is⊢⊢All₃ X


mutual
  ⊢⊢is⊢ctx : ∀ {Γ} → ⊢⊢ Γ → ⊢ Γ
  ⊢⊢is⊢ : ∀ {Γ A r} → Γ ⊢⊢ A ^ r → Γ ⊢ A ^ r
  ⊢⊢is⊢eq : ∀ {Γ A B r} → Γ ⊢⊢ A ≡ B ^ r → Γ ⊢ A ≡ B ^ r
  ⊢⊢is⊢term : ∀ {Γ A t r} → Γ ⊢⊢ t ∷ A ^ r → Γ ⊢ t ∷ A ^ r
  ⊢⊢is⊢eqterm : ∀ {Γ A t u r} → Γ ⊢⊢ t ≡ u ∷ A ^ r → Γ ⊢ t ≡ u ∷ A ^ r
  ⊢⊢is⊢All : ∀ {Γ ts As r} → Γ ⊢⊢All ts ∷ As ^ r → Γ ⊢All ts ∷ As ^ r
  ⊢⊢is⊢All≡ : ∀ {Γ ts us As r} → Γ ⊢⊢All ts ≡ us ∷ As ^ r → Γ ⊢All ts ≡ us ∷ As ^ r
  ⊢⊢is⊢All₃ : ∀ {Γ ts us As r} → All₃ (λ t u A → Γ ⊢⊢ t ≡ u ∷ A ^ r) ts us As
            → All₃ (λ t u A → Γ ⊢ t ≡ u ∷ A ^ r) ts us As
  
  ⊢⊢is⊢ctx ε = ε
  ⊢⊢is⊢ctx (⊢Γ ∙ x) = ⊢⊢is⊢ctx ⊢Γ ∙ ⊢⊢is⊢ x
  
  ⊢⊢is⊢ (Uⱼ x) = Uⱼ (⊢⊢is⊢ctx x)
  ⊢⊢is⊢ (univ x) = univ (⊢⊢is⊢term x)
  
  ⊢⊢is⊢eq (univ x) = univ (⊢⊢is⊢eqterm x)
  ⊢⊢is⊢eq (refl x) = refl (⊢⊢is⊢ x)
  ⊢⊢is⊢eq (sym X) = sym (⊢⊢is⊢eq X)
  ⊢⊢is⊢eq (trans X X₁) = trans (⊢⊢is⊢eq X) (⊢⊢is⊢eq X₁)
  
  ⊢⊢is⊢term (univ x ⊢Γ) = univ x (⊢⊢is⊢ctx ⊢Γ)
  ⊢⊢is⊢term (Indⱼ ⊢Γ ind∈) = Indⱼ (⊢⊢is⊢ctx ⊢Γ) ind∈
  ⊢⊢is⊢term (Emptyⱼ ⊢Γ) = Emptyⱼ (⊢⊢is⊢ctx ⊢Γ)
  ⊢⊢is⊢term (Πⱼ x ▹ x₁ ▹ X₁) =
    let ⊢G = ⊢⊢is⊢ X₁
        ⊢Γ , ⊢F = inversion-ctx (T.wf ⊢G)
    in Πⱼ x ▹ x₁ ▹ un-univ ⊢F ▹ un-univ ⊢G
  ⊢⊢is⊢term (var ⊢Γ x) = var (⊢⊢is⊢ctx ⊢Γ) x
  ⊢⊢is⊢term (lamⱼ x x₁ X) = let XX = ⊢⊢is⊢term X in lamⱼ x x₁ (let ⊢Γ , ⊢F = inversion-ctx (T.wfTerm XX) in ⊢F) XX
  ⊢⊢is⊢term (X₂ ∘ⱼ X₃) =
    let ⊢g = ⊢⊢is⊢term X₂ 
        ⊢a = ⊢⊢is⊢term X₃
        ⊢Π = un-univ (syntacticTerm ⊢g)
        rG , _ , l% , _ , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in  PE.subst (λ rr → rr PE.≡ % → _ PE.≡ ⁰ × _ PE.≡ ⁰) req l% ▹ un-univ (syntacticTerm ⊢a) ▹ PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G ▹ ⊢g ∘ⱼ ⊢a
  ⊢⊢is⊢term (fstⱼ X) = 
    let ⊢e = ⊢⊢is⊢term X
        l , _ , ⊢Π , ⊢Π' , e , er = inversion-Id (un-univ (syntacticTerm ⊢e))
        rG , _ , _ , ⊢A , ⊢B , _ , req , _ = inversion-Π ⊢Π
        rG' , _ , _ , ⊢A' , ⊢B' , _ , req' , _ = inversion-Π ⊢Π'
    in fstⱼ ⊢A (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢B) ⊢A' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢B') ⊢e
  ⊢⊢is⊢term (sndⱼ X) =
    let ⊢e = ⊢⊢is⊢term X
        l , _ , ⊢Π , ⊢Π' , e , er = inversion-Id (un-univ (syntacticTerm ⊢e))
        rG , _ , _ , ⊢A , ⊢B , _ , req , _ = inversion-Π ⊢Π
        rG' , _ , _ , ⊢A' , ⊢B' , _ , req' , _ = inversion-Π ⊢Π'
    in sndⱼ ⊢A (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢B) ⊢A' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢B') ⊢e
  ⊢⊢is⊢term (Ctrⱼ ⊢Γ ind∈ eq X) = Ctrⱼ (⊢⊢is⊢ctx ⊢Γ) ind∈ eq (⊢⊢is⊢All X)
  ⊢⊢is⊢term (IndRectⱼ x ind∈ X X₁ X₂) = IndRectⱼ x ind∈ (⊢⊢is⊢ X) (⊢⊢is⊢term X₁) (⊢⊢is⊢All X₂)
  ⊢⊢is⊢term (Emptyrecⱼ x X) = Emptyrecⱼ (⊢⊢is⊢ x) (⊢⊢is⊢term X)
  ⊢⊢is⊢term (Idⱼ X₁ X₂) =
    let ⊢t = (⊢⊢is⊢term X₁)
    in Idⱼ (un-univ (syntacticTerm ⊢t)) ⊢t (⊢⊢is⊢term X₂) 
  ⊢⊢is⊢term (Idreflⱼ X) = Idreflⱼ (⊢⊢is⊢term X)
  ⊢⊢is⊢term (transpⱼ x₁ X X₁ X₂ X₃) =
    let ⊢t = (⊢⊢is⊢term X)
    in transpⱼ (syntacticTerm ⊢t) (⊢⊢is⊢ x₁) ⊢t (⊢⊢is⊢term X₁) (⊢⊢is⊢term X₂) (⊢⊢is⊢term X₃)
  ⊢⊢is⊢term (castⱼ X₂ X₃) =
    let ⊢e = ⊢⊢is⊢term X₂
        ⊢Id = un-univ (syntacticTerm ⊢e)
        _ , ⊢U , ⊢A , ⊢B , _ = inversion-Id ⊢Id
        Ueq , _ = inversion-U ⊢U
        _ , leq , _ = Uinjectivity Ueq
    in castⱼ (PE.subst (λ l → _ ⊢ _ ∷ _ ^ [ ! , ι l ]) leq ⊢A) (PE.subst (λ l → _ ⊢ _ ∷ _ ^ [ ! , ι l ]) leq ⊢B) ⊢e (⊢⊢is⊢term X₃) 
  ⊢⊢is⊢term (conv X x) = conv (⊢⊢is⊢term X) (⊢⊢is⊢eq x)
  ⊢⊢is⊢term (equiv-eqⱼ ⊢Γ x) = equiv-eqⱼ (⊢⊢is⊢ctx ⊢Γ) x

  ⊢⊢is⊢eqterm (refl x) = refl (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (sym X) = sym (⊢⊢is⊢eqterm X)
  ⊢⊢is⊢eqterm (trans X X₁) = trans (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (conv X x) = conv (⊢⊢is⊢eqterm X) (⊢⊢is⊢eq x)
  ⊢⊢is⊢eqterm (Π-cong x x₁ X X₁) =
    let ⊢FH = ⊢⊢is⊢eq X
        ⊢F , _ = syntacticEq ⊢FH
    in Π-cong x x₁ ⊢F (un-univ≡ ⊢FH) (un-univ≡ (⊢⊢is⊢eq X₁))
  ⊢⊢is⊢eqterm (app-cong X X₁) = app-cong (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (β-red x x₁ x₃ x₄) =
    let ⊢t = ⊢⊢is⊢term x₃
    in β-red x x₁ (let ⊢Γ , ⊢F = inversion-ctx (T.wfTerm ⊢t) in ⊢F) ⊢t (⊢⊢is⊢term x₄)
  ⊢⊢is⊢eqterm (η-eq x₃ x₄ X) =
    let ⊢t = ⊢⊢is⊢term x₃
        ⊢Π = un-univ (syntacticTerm ⊢t)
        rG , l! , l% , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in η-eq (proj₁ (l! req)) (proj₂ (l! req)) (univ ⊢F) ⊢t (⊢⊢is⊢term x₄) (⊢⊢is⊢eqterm X)
  ⊢⊢is⊢eqterm (ctr-cong ⊢Γ ind∈ eq X) = ctr-cong (⊢⊢is⊢ctx ⊢Γ) ind∈ eq (⊢⊢is⊢All₃ X)
  ⊢⊢is⊢eqterm (IndRect-cong ind∈ x X X₁) = IndRect-cong ind∈ (⊢⊢is⊢eq x) (⊢⊢is⊢eqterm X) (⊢⊢is⊢All≡ X₁)
  ⊢⊢is⊢eqterm (IndRect-ctr≡ ind∈ eq x X X₁ nth≡) = IndRect-ctr≡ ind∈ eq (⊢⊢is⊢ x) (⊢⊢is⊢All X) (⊢⊢is⊢All X₁) nth≡
  ⊢⊢is⊢eqterm (Emptyrec-cong x x₁ x₂) = Emptyrec-cong (⊢⊢is⊢eq x) (⊢⊢is⊢term x₁) (⊢⊢is⊢term x₂)
  ⊢⊢is⊢eqterm (proof-irrelevance x x₁) = proof-irrelevance (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-cong X X₁ X₂) = Id-cong (un-univ≡ (⊢⊢is⊢eq X)) (⊢⊢is⊢eqterm X₁) (⊢⊢is⊢eqterm X₂)
  ⊢⊢is⊢eqterm (cast-refl X x x₁) = cast-refl (un-univ≡ (⊢⊢is⊢eq X)) (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (un-univ≡ (⊢⊢is⊢eq X)) (un-univ≡ (⊢⊢is⊢eq X₁)) (⊢⊢is⊢eqterm X₂) (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (cast-Π x₄ x₅) =
    let ⊢e = ⊢⊢is⊢term x₄
        ⊢Id = un-univ (syntacticTerm ⊢e)
        _ , _ , ⊢Π , ⊢Π' , _ = inversion-Id ⊢Id
        _ , _ , _ , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F' , ⊢G' , _ , req' , _ = inversion-Π ⊢Π'
    in cast-Π ⊢F (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G) ⊢F' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢G') ⊢e (⊢⊢is⊢term x₅)
  ⊢⊢is⊢eqterm (cast-equiv A∈ B∈ A≢B H x x₁) = cast-equiv A∈ B∈ A≢B H (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)

  ⊢⊢is⊢All εⱼ = εⱼ
  ⊢⊢is⊢All (consⱼ x X) = consⱼ (⊢⊢is⊢term x) (⊢⊢is⊢All X)

  ⊢⊢is⊢All≡ εⱼ = εⱼ
  ⊢⊢is⊢All≡ (consⱼ x X) = consⱼ (⊢⊢is⊢eqterm x) (⊢⊢is⊢All≡ X)

  ⊢⊢is⊢All₃ []ₐ = []ₐ
  ⊢⊢is⊢All₃ (x ∷ₐ X) = ⊢⊢is⊢eqterm x ∷ₐ ⊢⊢is⊢All₃ X
