{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.RelevanceUnicity (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Typed.EqRelInstance senv swf equivs
open import Definition.Untyped.Properties senv equivs using (subst-Univ-either)
open import Definition.Untyped senv equivs hiding (U≢Ind; U≢Π; U≢ne; Ind≢Π; Ind≢ne; Π≢ne; U≢Empty; Ind≢Empty; Empty≢Π; Empty≢ne)
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.Weakening senv equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
import Definition.Typed.Consequences.Inequality senv swf equivs as Ineq
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.PiNorm senv swf equivs
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (_⊎_; inj₁; inj₂)
import Tools.PropositionalEquality as PE

Ind-relevant-term : ∀ {Γ A r i} → Γ ⊢ Ind i ∷ A ^ r → Whnf A → A PE.≡ Univ ! ⁰
Ind-relevant-term [Ind] whnfA = let [[Ind]] , e = inversion-Ind [Ind]
                                in U≡A-whnf (sym (PE.subst (λ r → _ ⊢ _ ≡ _ ^ r) e [[Ind]])) whnfA

Ind-relevant : ∀ {Γ r i} → Γ ⊢ Ind i ^ r → r PE.≡ [ ! , ι ⁰ ]
Ind-relevant (univ [Ind]) = let er , el = Univ-PE-injectivity (Ind-relevant-term [Ind] Uₙ)
                            in PE.cong₂ (λ x y → [ x , ι y ]) er el

Empty-irrelevant-term : ∀ {Γ A r} → Γ ⊢ sEmpty ∷ A ^ r → Whnf A → A PE.≡ SProp
Empty-irrelevant-term [Empty] whnfA = let [[Empty]] , e = inversion-Empty [Empty]
                                      in U≡A-whnf (sym (PE.subst (λ r → _ ⊢ _ ≡ _ ^ r) e [[Empty]])) whnfA

Empty-irrelevant : ∀ {Γ r} → Γ ⊢ sEmpty  ^ r → r PE.≡ [ % , ι ⁰ ]
Empty-irrelevant (univ [Empty]) = let er , el = Univ-PE-injectivity (Empty-irrelevant-term [Empty] Uₙ)
                                  in PE.cong₂ (λ x y → [ x , ι y ]) er el

Univ-relevant-term : ∀ {Γ A rU lU r} → Γ ⊢ Univ rU lU ∷ A ^ r → Whnf A → A PE.≡ U ¹ × lU PE.≡ ⁰
Univ-relevant-term [U] whnfA = U≡A-whnf (sym (proj₁ (inversion-U [U]))) whnfA , proj₂ (proj₂ (inversion-U [U]))

Univ-relevant : ∀ {Γ rU lU r} → Γ ⊢ Univ rU lU ^ r → r PE.≡ [ ! , next lU ]
Univ-relevant (Uⱼ _) = PE.refl
Univ-relevant (univ [U]) = let er , el = Univ-PE-injectivity (proj₁ (Univ-relevant-term [U] Uₙ))
                           in PE.cong₂ (λ x y → [ x , y ]) er
                                       (PE.trans (PE.cong ι el) (PE.cong next (PE.sym  (proj₂ (Univ-relevant-term [U] Uₙ)))))
mutual 
  Univ-uniq′ : ∀ {Γ A T₁ T₂ r₁ r₂ l₁ l₁' l₂ l₂'} → Γ ⊢ T₁ ≡ Univ r₁ l₁ ^ [ ! , l₁' ] → Γ ⊢ T₂ ≡ Univ r₂ l₂ ^ [ ! , l₂' ]
    → next l₁ PE.≡ l₁' → next l₂ PE.≡ l₂'
    → ΠNorm A
    → Γ ⊢ A ∷ T₁ ^ [ ! , l₁' ] → Γ ⊢ A ∷ T₂ ^ [ ! , l₂' ] → r₁ PE.≡ r₂ × l₁' PE.≡ l₂' 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (univ 0<1 x₁) (univ 0<1 x₃) = 
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ PE.refl w (Indⱼ x _) y =
    let e₁′ , el₁′ , _ = Uinjectivity e₁
        e₂′ , el₂′ , _ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-Ind y)) )
    in PE.sym (PE.trans e₂′ e₁′) , PE.cong next (PE.sym el₂′)
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyⱼ x) y =
    let e₁′ , el₁′ , _ = Uinjectivity e₁
        e₂′ , el₂′ , _ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-Empty y)) ) 
    in PE.sym (PE.trans e₂′ e₁′) , PE.trans (PE.cong next (PE.sym el₂′)) el₂
  Univ-uniq′ e₁ e₂ el₁ el₂ (Πₙ w) (Πⱼ a ▹ b ▹ x ▹ x₁) (Πⱼ a' ▹ b' ▹ y ▹ y₁) =
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ Πirrₙ (Πⱼ a ▹ b ▹ x ▹ x₁) (Πⱼ a' ▹ b' ▹ y ▹ y₁) =
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ Idₙ (Idⱼ x x₁ x₂) (Idⱼ y y₁ y₂) = 
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in  PE.trans (PE.sym er₁) er₂ , PE.refl 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (var _ x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        _ , el = typelevel-injectivity e
        ⊢T≡T = PE.subst (λ T → _ ⊢ _ ≡ T ^ _) T≡T (refl (proj₁ (syntacticEq e₁)))
    in proj₁ (Uinjectivity (trans (trans (sym e₁) ⊢T≡T) (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , lx ]) (PE.sym el) e₂))) , el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (lamⱼ x x₁ x₂ X) y
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (∘ₙ n)) (_▹_▹_▹_∘ⱼ_ {G = G} _ _ _ x x₁) (_▹_▹_▹_∘ⱼ_ {G = G₁} _ _ _ y y₁) =
    let F≡F , rF≡rF , lF≡lF , lG≡lG , G≡G = injectivity (proj₂ (neTypeEq n x y))
        r≡r , _ = Uinjectivity (trans (sym e₁) (trans (substitutionEq G≡G (substRefl (singleSubst x₁)) (wfEq F≡F))
                                               (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , ι lx ]) (PE.sym lG≡lG) e₂))) 
    in r≡r , PE.cong ι lG≡lG
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (Ctrⱼ _ _ _ _) y
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyrecⱼ x x₁) (Emptyrecⱼ y y₁) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  -- IndRect gen-spine uses map: avoid IndRectₙ / IndRectⱼ–IndRectⱼ matching.
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne n) ⊢i@(IndRectⱼ _ _ _ _ _) y =
    let el , Teq = neTypeEq n ⊢i y
    in proj₁ (Uinjectivity (trans (sym e₁) (trans Teq (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ ! , lx ]) (PE.sym el) e₂)))) , el
  Univ-uniq′ e₁ e₂ el₁ el₂ w (castⱼ X X₁ X₂ X₃) (castⱼ y y₁ y₂ y₃) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ w (conv x x₁) y = Univ-uniq′ (trans x₁ e₁) e₂ el₁ el₂ w x y 
  Univ-uniq′ e₁ e₂ el₁ el₂ w x (conv y y₁) = Univ-uniq′ e₁ (trans y₁ e₂) el₁ el₂ w x y 
  
  Univ-uniq : ∀ {Γ A r₁ r₂ l₁ l₂} → ΠNorm A
    → Γ ⊢ A ∷ Univ r₁ l₁ ^ [ ! , next l₁ ] → Γ ⊢ A ∷ Univ r₂ l₂ ^ [ ! , next l₂ ] → r₁ PE.≡ r₂ × l₁ PE.≡ l₂
  Univ-uniq n ⊢A₁ ⊢A₂ =
    let ⊢Γ = wfTerm ⊢A₁
        er , el =  Univ-uniq′ (refl (Ugenⱼ ⊢Γ)) (refl (Ugenⱼ ⊢Γ)) PE.refl PE.refl n ⊢A₁ ⊢A₂
    in er , next-inj el
  
relevance-unicity′ : ∀ {Γ A r₁ r₂ l₁ l₂} → ΠNorm A → Γ ⊢ A ^ [ r₁ , l₁ ] → Γ ⊢ A ^ [ r₂ , l₂ ] → r₁ PE.≡ r₂ × l₁ PE.≡ l₂
relevance-unicity′ n (Uⱼ x) (Uⱼ x₁) = PE.refl , PE.refl 
relevance-unicity′ n (Uⱼ x) (univ x₁) = let _ , _ , ¹≡⁰ = inversion-U x₁ in ⊥-elim (⁰≢¹ (PE.sym  ¹≡⁰))
relevance-unicity′ n (univ x) (Uⱼ x₁) = let _ , _ , ¹≡⁰ = inversion-U x in ⊥-elim (⁰≢¹ (PE.sym  ¹≡⁰))
relevance-unicity′ n (univ x) (univ x₁) = let er , el = Univ-uniq n x x₁ in er , PE.cong ι el 

relevance-unicity : ∀ {Γ A r₁ r₂ l₁ l₂} → Γ ⊢ A ^ [ r₁ , l₁ ] → Γ ⊢ A ^ [ r₂ , l₂ ] → r₁ PE.≡ r₂ × l₁ PE.≡ l₂
relevance-unicity ⊢A₁ ⊢A₂ with doΠNorm ⊢A₁
... | _ with doΠNorm ⊢A₂
relevance-unicity ⊢A₁ ⊢A₂ | B , nB , ⊢B , rB | C , nC , ⊢C , rC =
  let e = detΠNorm* nB nC rB rC
  in relevance-unicity′ nC (PE.subst _ e ⊢B) ⊢C

-- inequalities at any relevance
U≢Ind : ∀ {r r′ l l′ i Γ} → Γ ⊢ Univ r l ≡ Ind i ^ [ r′ , l′ ] → ⊥
U≢Ind U≡Ind = Ineq.U≢Ind! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ])
                                    (proj₁ (typelevel-injectivity (Ind-relevant (proj₂ (syntacticEq U≡Ind)))))
                                    U≡Ind)

U≢Π : ∀ {rU lU  F rF G lF lG lΠ r Γ} → Γ ⊢ Univ rU lU ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r ^ [ r , ι lΠ ] → ⊥
U≢Π U≡Π =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq U≡Π)) (Ugenⱼ (wfEq U≡Π))
  in Ineq.U≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ rx ^ [ rx , _ ]) r≡! U≡Π)

U≢ne : ∀ {rU lU r l K Γ} → Neutral K → Γ ⊢ Univ rU lU ≡ K ^ [ r , ι l ] → ⊥
U≢ne neK U≡K =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq U≡K)) (Ugenⱼ (wfEq U≡K))
  in Ineq.U≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! U≡K)


Ind≢Π : ∀ {i F rF G lF lG r Γ} → Γ ⊢ Ind i ≡ Π F ^ rF ° lF ▹ G ° lG ° ⁰  ^ r ^ [ r , ι ⁰ ] → ⊥
Ind≢Π Ind≡Π =
  let r≡! , _ = typelevel-injectivity (Ind-relevant (proj₁ (syntacticEq Ind≡Π)))
  in Ineq.Ind≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ rx ^ [ rx , _ ]) r≡! Ind≡Π)

Empty≢Π : ∀ {F rF G lF r Γ} → Γ ⊢ sEmpty ≡ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ r ^ [ r , ι ⁰ ] → ⊥
Empty≢Π Empty≡Π =
  let r≡% , _ = relevance-unicity (proj₁ (syntacticEq Empty≡Π)) (univ (Emptyⱼ (wfEq Empty≡Π)))
  in Ineq.Empty≢Π% (PE.subst (λ rx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ rx ^ [ rx , _ ]) r≡% Empty≡Π)

Ind≢ne : ∀ {i K r Γ} → Neutral K → Γ ⊢ Ind i ≡ K ^ [ r , ι ⁰ ] → ⊥
Ind≢ne neK Ind≡K =
  let r≡! , _ = typelevel-injectivity (Ind-relevant (proj₁ (syntacticEq Ind≡K)))
  in Ineq.Ind≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! Ind≡K)

Empty≢ne : ∀ {K r Γ} → Neutral K → Γ ⊢ sEmpty ≡ K ^ [ r , ι ⁰ ] → ⊥
Empty≢ne neK Empty≡K =
  let r≡% , _ = relevance-unicity (proj₁ (syntacticEq Empty≡K)) (univ (Emptyⱼ (wfEq Empty≡K)))
  in Ineq.Empty≢ne% neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡% Empty≡K)

-- U != Empty is given easily by relevances
U≢Empty : ∀ {Γ rU lU r′} → Γ ⊢ Univ rU lU ≡ sEmpty ^ r′ → ⊥
U≢Empty U≡Empty =
  let ⊢U , ⊢Empty = syntacticEq U≡Empty
      e₁ , _ = relevance-unicity ⊢U (Ugenⱼ (wfEq U≡Empty))
      e₂ , _ = relevance-unicity ⊢Empty (univ (Emptyⱼ (wfEq U≡Empty)))
  in !≢% (PE.trans (PE.sym e₁) e₂)

-- Ind and Empty also by relevance
Ind≢Empty : ∀ {Γ i r} → Γ ⊢ Ind i ≡ sEmpty ^ r → ⊥
Ind≢Empty Ind≡Empty =
  let ⊢Ind , ⊢Empty = syntacticEq Ind≡Empty
      e₁ , _ = typelevel-injectivity (PE.trans (PE.sym (Ind-relevant ⊢Ind)) (Empty-irrelevant ⊢Empty))
  in !≢% e₁

relevance-uniq : ∀ {Γ t T₁ T₂ r₁ r₂ l₁ l₂} → Γ ⊢ t ∷ T₁ ^ [ r₁ , l₁ ] → Γ ⊢ t ∷ T₂ ^ [ r₂ , l₂ ] →
                 r₁ PE.≡ r₂
relevance-uniq (univ 0<1 x) (univ 0<1 x') = PE.refl 
relevance-uniq (Emptyⱼ x) (Emptyⱼ x₁) = PE.refl
relevance-uniq (Πⱼ x ▹ x₁ ▹ X ▹ X₁) (Πⱼ x₂ ▹ x₃ ▹ Y ▹ Y₁) =
          PE.refl 
relevance-uniq (Idⱼ X X₁ _) (Idⱼ Y Y₁ _) = PE.refl
relevance-uniq (Indⱼ x _) (Indⱼ y _) = PE.refl
relevance-uniq (var xx x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        er , el = typelevel-injectivity e
    in er
relevance-uniq (lamⱼ x x₁ x₂ X) (lamⱼ y y₁ y₂ Y) =
  let erF , elF  = relevance-unicity x₂ y₂
  in relevance-uniq X (PE.subst₂ (λ r l → _ ∙ _ ^ [ r , ι l ] ⊢ _ ∷ _ ^ _) (PE.sym erF) (PE.sym (ιinj elF)) Y)
relevance-uniq (_ ▹ _ ▹ _ ▹ X ∘ⱼ X₁) (_ ▹ _ ▹ _ ▹ Y ∘ⱼ Y₁) = relevance-uniq X Y
relevance-uniq (fstⱼ X X₁ X₂ _ _) (fstⱼ Y Y₁ Y₂ _ _) =
    PE.refl 
relevance-uniq (sndⱼ X X₁ X₂ _ _) (sndⱼ Y Y₁ Y₂ _ _) = PE.refl
relevance-uniq (Ctrⱼ _ _ _ _) Y = PE.sym (proj₁ (ctrTypeEq′ Y))
relevance-uniq (Emptyrecⱼ x X) (Emptyrecⱼ y Y) = let er , el = relevance-unicity x y in er
relevance-uniq (IndRectⱼ _ _ x _ _) Y = proj₁ (relevance-unicity x (proj₁ (IndRectTypeEq′ Y)))
relevance-uniq (equiv-eqⱼ x _) (equiv-eqⱼ x₁ _) = PE.refl
relevance-uniq (Idreflⱼ X) (Idreflⱼ Y) =
    PE.refl 
relevance-uniq (transpⱼ x x₁ X X₁ X₂ X₃) (transpⱼ x₂ x₃ Y Y₁ Y₂ Y₃) =
    PE.refl 
relevance-uniq (castⱼ X X₁ X₂ X₃) (castⱼ Y Y₁ Y₂ Y₃) = relevance-uniq X₃ Y₃
relevance-uniq (conv X x) Y = relevance-uniq X Y
relevance-uniq X (conv Y y) = relevance-uniq X Y
  