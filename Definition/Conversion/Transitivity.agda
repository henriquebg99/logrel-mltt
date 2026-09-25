import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.Transitivity (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv
open import Definition.Untyped.Properties senv
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.RedSteps senv equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.Conversion senv swf equivs
open import Definition.Conversion.ConvSize senv equivs
open import Definition.Conversion.ConversionProp senv swf equivs
open import Definition.Conversion.StabilityProp senv swf equivs
open import Definition.Conversion.Inversion senv swf equivs
open import Definition.Typed.Consequences.IndRectCong senv swf equivs using (indRectBranchTyListCong)
open import Definition.Conversion.Whnf senv swf equivs
open import Definition.Conversion.TransitivityHelper
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Reduction senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
import Definition.Typed.Consequences.Inequality senv swf equivs as WF
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.SucCong senv swf equivs
open import Definition.Typed.Consequences.RelevanceUnicity senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Tools.Nat
open import Tools.List using (All₂; []ₐ; _∷ₐ_)
open import Tools.Product
open import Tools.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Tools.Empty
import Tools.PropositionalEquality as PE

-- At a neutral type the only [conv↓] rule is ne-ins.  Matching on this view
-- (instead of nesting ne-ins inside cast-refl/cast-refl') spares the coverage
-- checker from refuting every other [conv↓] rule in every clause, which it does
-- by an expensive emptiness search.
private
  data NeIns {Γ t u A ll} : Γ ⊢ t [conv↓] u ∷ A ^ ι ll → Set where
    isNeIns : ∀ {M} (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ll ]) (⊢u : Γ ⊢ u ∷ A ^ [ ! , ι ll ])
              (neA : Neutral A) (t~u : Γ ⊢ t ~ u ↓! M ^ ι ll)
            → NeIns (ne-ins ⊢t ⊢u neA t~u)

  neIns : ∀ {Γ t u A ll} → Neutral A → (c : Γ ⊢ t [conv↓] u ∷ A ^ ι ll) → NeIns c
  neIns _ (ne-ins ⊢t ⊢u neA t~u) = isNeIns ⊢t ⊢u neA t~u
  neIns () (ne _)
  neIns () (ℕ-refl _)
  neIns () (Empty-refl _)
  neIns () (Ind-refl _)
  neIns () (Π-cong _ _ _ _ _ _ _ _ _)
  neIns () (Id-cong _ _ _)
  neIns () (ℕ-ins _)
  neIns () (Ind-ins _)
  neIns () (zero-refl _)
  neIns () (suc-cong _)
  neIns () (η-eq _ _ _ _ _ _ _ _)
  neIns () (ctr-cong _ _ _ _ _)

  neˡ : ∀ {Γ t u A l} → Γ ⊢ t ~ u ↓! A ^ l → Neutral t
  neˡ t~u = proj₁ (proj₂ (ne~↓! t~u))

  neʳ : ∀ {Γ t u A l} → Γ ⊢ t ~ u ↓! A ^ l → Neutral u
  neʳ t~u = proj₂ (proj₂ (ne~↓! t~u))

  ¬neℕ : Neutral ℕ → ⊥
  ¬neℕ ()

  ¬neΠ : ∀ {F r lF G lG l r'} → Neutral (Π F ^ r ° lF ▹ G ° lG ° l ^ r') → ⊥
  ¬neΠ ()

  ¬neInd : ∀ {i} → Neutral (Ind i) → ⊥
  ¬neInd ()

abstract
  mutual
  
    -- Transitivity of algorithmic equality of neutrals.
    trans~↑! : ∀ {n t u v A B Γ Δ l l'}
           → l PE.≡ l'
           → ⊢ Γ ≡ Δ
           → (e : Γ ⊢ t ~ u ↑! A ^ l)
           → (e' : Δ ⊢ u ~ v ↑! B ^ l')
           → (size~↑! e + size~↑! e') << n
           → ∃₂ λ C (e'' : Γ ⊢ t ~ v ↑! C ^ l) → Γ ⊢ A ≡ C ^ [ ! , l ] × Γ ⊢ C ≡ B ^ [ ! , l ] × size~↑! e'' <= (size~↑! e + size~↑! e')
  
    trans~↑! {n = 0} el Γ≡Δ X Y ()
  
    trans~↑! {n = 1+ n} el Γ≡Δ (var-refl x₁ x≡y) (var-refl x₂ x≡y₁) e =
      _ , var-refl x₁ (PE.trans x≡y x≡y₁)
      , refl (syntacticTerm x₁) ,
        proj₂ (neTypeEq (var _) x₁
                  (PE.subst (λ x → _ ⊢ var x ∷ _ ^ _) (PE.sym x≡y)
                           (stabilityTerm (symConEq Γ≡Δ) (PE.subst (λ lx → _ ⊢ _ ∷ _ ^ [ ! , lx ]) (PE.sym el) x₂)))) ,
        leS le0                   
  
    trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (app-cong {k = k} {rF = !} {lΠ = lΠ} t~u a<>b) (app-cong {l = l} {rF = !} u~v b<>c) (leS e) =
      let C , wC , t~v , ΠFG≡C , C≡ΠF′G′ , sizet~u = trans~↓! {n = n} PE.refl Γ≡Δ t~u u~v (<<-trans (<=-help-ab' {a = size~↓! t~u} {b = size~↓! u~v}) e)
          H , E , C≡ΠHE = Π≡A ΠFG≡C wC
          ⊢Γ = proj₁ (contextConvSubst Γ≡Δ)
          ΠFG≡C' = PE.subst (λ X → _ ⊢ _ ≡ X ^ [ ! , ι _ ]) C≡ΠHE ΠFG≡C
          C≡ΠF′G′' = PE.subst (λ X → _ ⊢ X ≡ _ ^ [ ! , ι _ ]) C≡ΠHE C≡ΠF′G′
          F≡F₁ , rF≡rF₁ , _ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡C'
          F≡F₁' , rF≡rF₁' , lF≡lF₁' , lG≡lG₁' , G≡G₁' = injectivity C≡ΠF′G′'
          t~v' = PE.subst (λ X →  Γ ⊢ k ~ l ↓! X ^ ι lΠ) C≡ΠHE t~v
          a<>c , sizea<>c = transConv↑Term {n = n} (PE.cong ι lF≡lF₁') Γ≡Δ (trans F≡F₁ F≡F₁') a<>b b<>c
                                (<<-trans (<=-help-ab'' {a = size~↓! t~u} {c = size~↓! u~v}) e) 
          t≡v = soundnessConv↑Term a<>b
          _ , ⊢t , _ = syntacticEqTerm t≡v
      in _ , app-cong t~v' (convConv↑Term (reflConEq ⊢Γ) F≡F₁ a<>c) ,
         substTypeEq G≡G₁ (refl ⊢t) , substTypeEq G≡G₁' (conv t≡v F≡F₁) ,
         PE.subst₂ (λ X Y → 1+ (X + Y) <= (size~↑! (app-cong t~u a<>b) + size~↑! (app-cong u~v b<>c)))
                   (PE.sym (sizeSubst-gen  (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓! t~v C≡ΠHE)) (PE.sym (convConv↑TermSize (reflConEq ⊢Γ) F≡F₁ a<>c))
                   (leS (<=-trans (<=-cong-+ sizet~u sizea<>c) (<=-help-3-abcd {a = size~↓! t~u} {b = size~↓! u~v}))) 
  
    trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (app-cong {k = k} {rF = %} {lΠ = lΠ} t~u a<>b) (app-cong {l = l} {rF = %} u~v b<>c) (leS e) =
      let C , wC , t~v , ΠFG≡C , C≡ΠF′G′ , sizet~u = trans~↓! {n = n} PE.refl Γ≡Δ t~u u~v (<<-trans (<=-help-ab' {a = size~↓! t~u} {b = size~↓! u~v}) e)
          H , E , C≡ΠHE = Π≡A ΠFG≡C wC
          ⊢Γ = proj₁ (contextConvSubst Γ≡Δ)
          ΠFG≡C' = PE.subst (λ X → _ ⊢ _ ≡ X ^ [ ! , ι _ ]) C≡ΠHE ΠFG≡C
          C≡ΠF′G′' = PE.subst (λ X → _ ⊢ X ≡ _ ^ [ ! , ι _ ]) C≡ΠHE C≡ΠF′G′
          F≡F₁ , rF≡rF₁ , _ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡C'
          F≡F₁' , rF≡rF₁' , lF≡lF₁' , lG≡lG₁' , G≡G₁' = injectivity C≡ΠF′G′'
          t~v' = PE.subst (λ X →  Γ ⊢ k ~ l ↓! X ^ ι lΠ) C≡ΠHE t~v
          a<>c = trans~↑% Γ≡Δ a<>b
                              (conv~↑% (PE.subst (λ x → _ ⊢ _ ~ _ ↑% _ ^ ι x) (PE.sym lF≡lF₁') b<>c)
                              (stabilityEq Γ≡Δ (sym (trans F≡F₁ F≡F₁'))))
          _ , _ , t≡v = soundness~↑% a<>b
          _ , ⊢t , _ = syntacticEqTerm t≡v
      in _ , app-cong t~v' (conv~↑% a<>c F≡F₁) ,
         substTypeEq G≡G₁ (proof-irrelevance ⊢t ⊢t) ,
         substTypeEq G≡G₁' (conv t≡v F≡F₁) ,
         PE.subst (λ X → 1+ (X + 1) <= (size~↑! (app-cong t~u a<>b) + size~↑! (app-cong u~v b<>c)))
                  (PE.sym (sizeSubst-gen  (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓! t~v C≡ΠHE))
                  (leS (<=-trans (<=-cong-+ sizet~u (le-refl 1)) (leS (<=-help-abcd-b {c = size~↓! u~v}))))
                   
    trans~↑! el Γ≡Δ (app-cong {rF = !} t~u a<>b) (app-cong {rF = %} u~v b<>c) e =
     let whnfA , neK , neL = ne~↓! t~u
         ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
         ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
         _ , ΠFG≡ΠF₂G₂ = neTypeEq neL ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
         F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
     in ⊥-elim (relevance-discr rF≡rF₂)
  
    trans~↑! el Γ≡Δ (app-cong {rF = %} t~u a<>b) (app-cong {rF = !} u~v b<>c) e =
     let whnfA , neK , neL = ne~↓! t~u
         ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
         ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
         _ , ΠFG≡ΠF₂G₂ = neTypeEq neL ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
         F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
     in ⊥-elim (relevance-discr (PE.sym rF≡rF₂))
  
    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (natrec-cong {k = k} A<>B a₀<>b₀ aₛ<>bₛ t~u) (natrec-cong {l = l} B<>C b₀<>c₀ bₛ<>cₛ u~v) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          A≡B = soundnessConv↑ A<>B
          F[0]≡F₁[0] = substTypeEq A≡B (refl (zeroⱼ ⊢Γ))
          ΠℕFs≡ΠℕF₁s = sucCong A≡B
          A<>C , sizeA<>C = transConv↑ {n = n} (Γ≡Δ ∙ (refl (univ (ℕⱼ ⊢Γ)))) A<>B B<>C
                                       (<<-trans (leS (<=-help-nat-cong-ab {b = sizeConv↑ B<>C})) e)
          a₀<>c₀ , sizea₀<>c₀ = transConv↑Term {n = n} PE.refl Γ≡Δ F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
                                               (<<-trans (<=-help-nat-congb'c' {a = sizeConv↑ A<>B} {b = sizeConv↑ B<>C}) e) 
          aₛ<>cₛ , sizeaₛ<>cₛ = transConv↑Term {n = n} PE.refl Γ≡Δ ΠℕFs≡ΠℕF₁s aₛ<>bₛ bₛ<>cₛ
                                               (<<-trans (<=-help-nat-congb''c'' {a = sizeConv↑ A<>B} {b = sizeConv↑ B<>C}) e)
          C , wC ,  t~v , ℕ≡C , _ , sizet~v = trans~↓! {n = n} PE.refl Γ≡Δ t~u u~v
                                                       (<<-trans (<=-help-nat-congb'''c''' {a = sizeConv↑ A<>B} {b = sizeConv↑ B<>C}) e)
          ℕ≡C' = ℕ≡A ℕ≡C wC
      in  _ , natrec-cong A<>C a₀<>c₀ aₛ<>cₛ (PE.subst (λ X → Γ ⊢ k ~ l ↓! X ^ ι ⁰) ℕ≡C' t~v) ,
          substTypeEq (refl (proj₁ (syntacticEq A≡B))) (refl (proj₁ (proj₂ (syntacticEqTerm (soundness~↓! t~u))))) ,
          substTypeEq A≡B (soundness~↓! t~u) ,
          leS (<=-trans (<=-cong-+4 sizeA<>C sizea₀<>c₀ sizeaₛ<>cₛ
                                    (<=-trans (≡-to-<= (sizeSubst-gen (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι _) size~↓! t~v ℕ≡C'))
                                              sizet~v))
              (<=-help-nat-cong {a = sizeConv↑ A<>B} {b = sizeConv↑ B<>C}))
  
    -- IndRect uses a map-spine: dual IndRect-cong matching does not unify, so we
    -- generalize the middle term with a propositional equation (cf. ctr in
    -- Definition.LogicalRelation.Properties.Transitivity).
    -- Split on lG so go's level is rigid: a flexible ι lG overlaps every ι ⁰
    -- constructor with the IndRect map-spine and makes coverage checking diverge.
    trans~↑! {n = 1+ n} {Γ = Γ} {Δ = Δ} PE.refl Γ≡Δ (IndRect-cong {ind} {P} {P'} {t} {t'} {ms} {ms'} {lG = ⁰} ind∈ x x₁ x₂) u~v sz =
      go u~v PE.refl sz
      where
        transAll : ∀ {Γ ts ts' ts'' As l}
                 → Γ ⊢All ts ≡ ts' ∷ As ^ [ ! , l ]
                 → Γ ⊢All ts' ≡ ts'' ∷ As ^ [ ! , l ]
                 → Γ ⊢All ts ≡ ts'' ∷ As ^ [ ! , l ]
        transAll εⱼ εⱼ = εⱼ
        transAll (consⱼ t≡t' ts≡ts') (consⱼ t'≡t'' ts'≡ts'') =
          consⱼ (trans t≡t' t'≡t'') (transAll ts≡ts' ts'≡ts'')
  
        go : ∀ {u v B} (e' : Δ ⊢ u ~ v ↑! B ^ ι ⁰)
           → u PE.≡ IndRect (SI.SInd.name ind) ⁰ P' t' ms'
           → (size~↑! (IndRect-cong ind∈ x x₁ x₂) + size~↑! e') << (1+ n)
           → ∃₂ λ C (e'' : Γ ⊢ IndRect (SI.SInd.name ind) ⁰ P t ms ~ v ↑! C ^ ι ⁰)
                → Γ ⊢ (P [ t ]) ≡ C ^ [ ! , ι ⁰ ] × Γ ⊢ C ≡ B ^ [ ! , ι ⁰ ]
                × size~↑! e'' <= (size~↑! (IndRect-cong ind∈ x x₁ x₂) + size~↑! e')
  
        go (IndRect-cong ind∈′ y y₁ y₂) eq (leS e) with IndRect-PE-injectivity eq
        ... | name≡ , PE.refl , PE.refl , PE.refl , PE.refl
             with SI.name-inj senv (proj₁ swf) ind∈′ ind∈ name≡
        ... | PE.refl =
          let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
              P<>P'' , sizeP<>P'' = transConv↑ {n = n} (Γ≡Δ ∙ (refl (univ (Indⱼ ⊢Γ)))) x y
                                               (<<-trans (<=-help-ab' {a = sizeConv↑ x} {b = sizeConv↑ y} {c = size~↓! x₁} {d = size~↓! y₁}) e)
              C , wC , t~t'' , Ind≡C , _ , sizet~t'' = trans~↓! {n = n} PE.refl Γ≡Δ x₁ y₁
                                                               (<<-trans (<=-help-ab'' {a = sizeConv↑ x} {b = size~↓! x₁} {c = sizeConv↑ y} {d = size~↓! y₁}) e)
              t~tInd = [~] (_⊢_~_↓!_^_.A t~t'')
                           (PE.subst (λ X → Γ ⊢ _⊢_~_↓!_^_.A t~t'' ⇒* X ^ [ ! , ι ⁰ ])
                                     (Ind≡A Ind≡C wC) (_⊢_~_↓!_^_.D t~t''))
                           Indₙ (_⊢_~_↓!_^_.k~l t~t'')
              ms≡ms'' = transAll x₂ (indRectBranchTyListCong ind∈ (sym (soundnessConv↑ x))
                                                                  (stabilityAll≡ (symConEq Γ≡Δ) y₂))
              Pt≡P't' = substTypeEq (soundnessConv↑ x) (soundness~↓! x₁)
          in  _ , IndRect-cong ind∈ P<>P'' t~tInd ms≡ms'' ,
              refl (proj₁ (syntacticEq Pt≡P't')) , Pt≡P't' ,
              leS (<=-trans (<=-cong-+ sizeP<>P'' sizet~t'')
                            (<=-help-3-abcd {a = sizeConv↑ x} {b = sizeConv↑ y} {c = size~↓! x₁} {d = size~↓! y₁}))
  
        go (cast-refl' A~B c x₄) PE.refl (leS e) with neIns (proj₂ (proj₂ (ne~↓! A~B))) c
        ... | isNeIns x' x₁' x₂' ([~] K D whK u~v) =
          let net , neu = ne~↑! (IndRect-cong ind∈ x x₁ x₂)
              t≡u = soundness~↑! (IndRect-cong ind∈ x x₁ x₂)
              _ , neB , neA = ne~↓! A~B
              ⊢A , ⊢t , ⊢u = syntacticEqTerm t≡u
              _ , A≡B = neTypeEq neu ⊢u (stabilityTerm (symConEq Γ≡Δ) x')
              _ , ⊢B = syntacticEq A≡B
              C , t~v' , A≡C , C≡B , sizet~v' = trans~↑! {n = n} PE.refl Γ≡Δ (IndRect-cong ind∈ x x₁ x₂) u~v
                                                         (<=-trans (<=-help-abc {a = size~↑! (IndRect-cong ind∈ x x₁ x₂)} {b = size~↓! A~B} {c = size~↑! u~v}) e)
              _ , ⊢C = syntacticEq A≡C
              XC , wXC , DXC = whNorm ⊢C
              t[conv↑]v = ne-ins (conv ⊢t A≡B) (stabilityTerm (symConEq Γ≡Δ) x₁') neA ([~] _ (red DXC) wXC t~v')
          in _ , cast-refl' (stability~↓! (symConEq Γ≡Δ) A~B) t[conv↑]v (stabilityTerm (symConEq Γ≡Δ) x₄) ,
             A≡B , refl ⊢B ,
             <=-trans (<=-cong-+ (leS (≡-to-<= (stabilitySize~↓! (symConEq Γ≡Δ) A~B))) (leS (leS sizet~v')))
                      (<=-help-2-2 {a = size~↑! (IndRect-cong ind∈ x x₁ x₂)} {b = size~↑! (_⊢_~_↓!_^_.k~l A~B)} {c = size~↑! u~v})
  
        go (castℕ-refl' ([~] A D whnfB u~v) x₃) PE.refl (leS e) =
          let C , t~v , A≡C , C≡B , sizet~v = trans~↑! {n = n} PE.refl Γ≡Δ (IndRect-cong ind∈ x x₁ x₂) u~v
                                                         (<=-trans (<=-help-1-2 {a = size~↑! (IndRect-cong ind∈ x x₁ x₂)} {b = size~↑! u~v}) e)
              _ , ⊢C = syntacticEq A≡C
              X , wX , DX = whNorm ⊢C
              eqℕ = ℕ≡A (trans (sym (subset* D)) (trans (stabilityEq Γ≡Δ (sym C≡B)) (stabilityEq Γ≡Δ (subset* (red DX))))) wX
              DN = PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqℕ (red DX)
              A≡ℕ = trans A≡C (trans C≡B (stabilityEq (symConEq Γ≡Δ) (subset* D)))
          in _ , castℕ-refl' ([~] _ DN ℕₙ t~v) (stabilityTerm (symConEq Γ≡Δ) x₃) , A≡ℕ , refl (proj₁ (syntacticEq (sym A≡ℕ))) ,
             <=-trans (leS (leS sizet~v)) (<=-help-2 {a = size~↑! (IndRect-cong ind∈ x x₁ x₂)} {b = size~↑! u~v})
  
        go (castInd-refl' ([~] A D whnfB u~v) x₃) PE.refl (leS e) =
          let C , t~v , A≡C , C≡B , sizet~v = trans~↑! {n = n} PE.refl Γ≡Δ (IndRect-cong ind∈ x x₁ x₂) u~v
                                                         (<=-trans (<=-help-1-2 {a = size~↑! (IndRect-cong ind∈ x x₁ x₂)} {b = size~↑! u~v}) e)
              _ , ⊢C = syntacticEq A≡C
              X , wX , DX = whNorm ⊢C
              eqInd = Ind≡A (trans (sym (subset* D)) (trans (stabilityEq Γ≡Δ (sym C≡B)) (stabilityEq Γ≡Δ (subset* (red DX))))) wX
              DN = PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqInd (red DX)
              A≡Ind = trans A≡C (trans C≡B (stabilityEq (symConEq Γ≡Δ) (subset* D)))
          in _ , castInd-refl' ([~] _ DN Indₙ t~v) (stabilityTerm (symConEq Γ≡Δ) x₃) , A≡Ind , refl (proj₁ (syntacticEq (sym A≡Ind))) ,
             <=-trans (leS (leS sizet~v)) (<=-help-2 {a = size~↑! (IndRect-cong ind∈ x x₁ x₂)} {b = size~↑! u~v})
  
        go (var-refl _ _) ()
        go (app-cong _ _) ()
        go (natrec-cong _ _ _ _) ()
        go (Emptyrec-cong _ _) ()
        go (cast-cong _ _ _ _ _) ()
        go (cast-refl _ _ _) ()
        go (castℕ-refl _ _) ()
        go (castInd-refl _ _) ()
        go (cast-neℕ _ _ _ _) ()
        go (cast-ℕ _ _ _ _) ()
        go (cast-neΠ _ _ _ _ _) ()
        go (cast-Π _ _ _ _ _) ()
        go (cast-Πℕ _ _ _ _) ()
        go (cast-ℕΠ _ _ _ _) ()
        go (cast-ΠΠ%! _ _ _ _ _) ()
        go (cast-ΠΠ!% _ _ _ _ _) ()
        go (cast-neInd _ _ _ _) ()
        go (cast-Ind _ _ _ _) ()
        go (cast-IndΠ _ _ _ _) ()
        go (cast-ΠInd _ _ _ _) ()
        go (cast-Indℕ _ _ _) ()
        go (cast-ℕInd _ _ _) ()
        go (cast-IndInd _ _ _ _) ()

    trans~↑! {n = 1+ n} {Γ = Γ} {Δ = Δ} PE.refl Γ≡Δ (IndRect-cong {ind} {P} {P'} {t} {t'} {ms} {ms'} {lG = ¹} ind∈ x x₁ x₂) u~v sz =
      go u~v PE.refl sz
      where
        transAll : ∀ {Γ ts ts' ts'' As l}
                 → Γ ⊢All ts ≡ ts' ∷ As ^ [ ! , l ]
                 → Γ ⊢All ts' ≡ ts'' ∷ As ^ [ ! , l ]
                 → Γ ⊢All ts ≡ ts'' ∷ As ^ [ ! , l ]
        transAll εⱼ εⱼ = εⱼ
        transAll (consⱼ t≡t' ts≡ts') (consⱼ t'≡t'' ts'≡ts'') =
          consⱼ (trans t≡t' t'≡t'') (transAll ts≡ts' ts'≡ts'')
  
        go : ∀ {u v B} (e' : Δ ⊢ u ~ v ↑! B ^ ι ¹)
           → u PE.≡ IndRect (SI.SInd.name ind) ¹ P' t' ms'
           → (size~↑! (IndRect-cong ind∈ x x₁ x₂) + size~↑! e') << (1+ n)
           → ∃₂ λ C (e'' : Γ ⊢ IndRect (SI.SInd.name ind) ¹ P t ms ~ v ↑! C ^ ι ¹)
                → Γ ⊢ (P [ t ]) ≡ C ^ [ ! , ι ¹ ] × Γ ⊢ C ≡ B ^ [ ! , ι ¹ ]
                × size~↑! e'' <= (size~↑! (IndRect-cong ind∈ x x₁ x₂) + size~↑! e')
  
        go (IndRect-cong ind∈′ y y₁ y₂) eq (leS e) with IndRect-PE-injectivity eq
        ... | name≡ , PE.refl , PE.refl , PE.refl , PE.refl
             with SI.name-inj senv (proj₁ swf) ind∈′ ind∈ name≡
        ... | PE.refl =
          let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
              P<>P'' , sizeP<>P'' = transConv↑ {n = n} (Γ≡Δ ∙ (refl (univ (Indⱼ ⊢Γ)))) x y
                                               (<<-trans (<=-help-ab' {a = sizeConv↑ x} {b = sizeConv↑ y} {c = size~↓! x₁} {d = size~↓! y₁}) e)
              C , wC , t~t'' , Ind≡C , _ , sizet~t'' = trans~↓! {n = n} PE.refl Γ≡Δ x₁ y₁
                                                               (<<-trans (<=-help-ab'' {a = sizeConv↑ x} {b = size~↓! x₁} {c = sizeConv↑ y} {d = size~↓! y₁}) e)
              t~tInd = [~] (_⊢_~_↓!_^_.A t~t'')
                           (PE.subst (λ X → Γ ⊢ _⊢_~_↓!_^_.A t~t'' ⇒* X ^ [ ! , ι ⁰ ])
                                     (Ind≡A Ind≡C wC) (_⊢_~_↓!_^_.D t~t''))
                           Indₙ (_⊢_~_↓!_^_.k~l t~t'')
              ms≡ms'' = transAll x₂ (indRectBranchTyListCong ind∈ (sym (soundnessConv↑ x))
                                                                  (stabilityAll≡ (symConEq Γ≡Δ) y₂))
              Pt≡P't' = substTypeEq (soundnessConv↑ x) (soundness~↓! x₁)
          in  _ , IndRect-cong ind∈ P<>P'' t~tInd ms≡ms'' ,
              refl (proj₁ (syntacticEq Pt≡P't')) , Pt≡P't' ,
              leS (<=-trans (<=-cong-+ sizeP<>P'' sizet~t'')
                            (<=-help-3-abcd {a = sizeConv↑ x} {b = sizeConv↑ y} {c = size~↓! x₁} {d = size~↓! y₁}))
  
        go (var-refl _ _) ()
        go (app-cong _ _) ()
        go (natrec-cong _ _ _ _) ()
        go (Emptyrec-cong _ _) ()
  
    trans~↑! {n = 1+ n} PE.refl Γ≡Δ (Emptyrec-cong A<>B t~u) (Emptyrec-cong B<>C u~v) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          A≡B = soundnessConv↑ A<>B
          A<>C , sizeA<>C = transConv↑ {n = n} Γ≡Δ A<>B B<>C
                                       (<<-trans (leS <=-help-ab1') e)
          ⊢t , ⊢u , t≡u = soundness~↑% t~u
          _ , ⊢v , u≡v = soundness~↑% u~v
          t~v = %~↑ ⊢t (stabilityTerm (symConEq Γ≡Δ) ⊢v)
      in _ , Emptyrec-cong A<>C t~v , refl (proj₁ (syntacticEq A≡B)) , A≡B ,
        leS (<=-trans sizeA<>C (leS <=-help-ab1') )    
  
    trans~↑! {n = 1+ n} {A = AA} {Γ = Γ} {Δ = Δ} el Γ≡Δ (cast-cong {A = A} X x x₁ x₂ x₃) (cast-cong {A' = A'} {B' = B'} Y x₄ x₅ x₆ x₇) (leS e) =
      let K , wK , XY , [U] , _ , sizeXY = trans~↓! {n = n} PE.refl Γ≡Δ X Y (<<bind-suc (<=-help-id-cong {b = size~↓! Y}) e)
          eqU = U≡A-whnf [U] wK
          XY' = PE.subst (λ X →  Γ ⊢ A ~ A' ↓! X ^ ι ¹) eqU XY
          X≡Y = univ (soundness~↓! XY')
          Y≡Y = univ (soundness~↓! Y)
          K' , wK' , t~t , [U]' , _ , sizet~t = trans~↓! {n = n} PE.refl (symConEq Γ≡Δ) x₄ x (<<bind-suc (<=-help-3-ab'c {b =  size~↓! Y} {c' = sizeConv↓Term x₁}) e)
          eqU' = U≡A-whnf [U]' wK'
          t~t' = PE.subst (λ X → Γ ⊢ B' ~ AA ↓! X ^ ι ¹) eqU' (stability~↓! (symConEq Γ≡Δ) t~t)
          _ , _ , neA = ne~↓! Y
          u~u , sizeu~u = transConv↓Term {n = n} Γ≡Δ (trans X≡Y (sym (stabilityEq (symConEq Γ≡Δ) Y≡Y))) PE.refl x₁ x₅ (<<-trans (<=-help-b''c'' {a =  size~↓! X} {b =  size~↓! Y}) e)
          A₁≡B = (trans (sym (soundness~↓! t~t')) (soundness~↓! (stability~↓! (symConEq Γ≡Δ) x₄)))
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X →  Γ ⊢ A ~ A' ↓! X ^ ι ¹) size~↓! XY eqU)) sizeXY
          sizet~t' = <=-trans (≡-to-<= (PE.trans (sizeSubst-gen (λ X → Γ ⊢ _ ~ _ ↓! X ^ ι ¹) size~↓!
                                                 (stability~↓! (symConEq Γ≡Δ) t~t) eqU') (stabilitySize~↓! (symConEq Γ≡Δ) t~t)))
                              sizet~t
      in _ , cast-cong XY' t~t' u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) ,
         refl (univ (proj₁ (proj₂ (syntacticEqTerm A₁≡B)))) , univ A₁≡B ,
         leS (<=-trans (<=-cong-+3 sizeXY' sizet~t' sizeu~u)
                       (<=-help-id-cong'' {a =  size~↓! X}))
  
    trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (cast-ℕ {A = A} X x x₁ x₂) (cast-ℕ {A' = A'} Y x₃ x₄ x₅) (leS e) =
      let K , wK , XY- , [U] , _ , sizeXY = trans~↓! {n = n} PE.refl (symConEq Γ≡Δ) Y X (<<bind-suc <=-help-ab'- e)
          eqU = U≡A-whnf [U] wK
          XY = stability~↓! (symConEq Γ≡Δ) XY-
          XY' = PE.subst (λ X →  Γ ⊢ A' ~ A ↓! X ^ ι ¹) eqU XY
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x x₃ (<<-trans (<=-help-ab'' {a = size~↓! X} {c = size~↓! Y}) e) 
          sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X →  Γ ⊢ A' ~ A ↓! X ^ ι ¹) size~↓! XY eqU)) (<=-trans (≡-to-<= (stabilitySize~↓! (symConEq Γ≡Δ) XY-)) sizeXY) 
      in _ , cast-ℕ XY' t~t x₁ (stabilityTerm (symConEq Γ≡Δ) x₅) , refl (proj₂ (syntacticEq (univ (soundness~↓! X)))) , sym (univ (soundness~↓! X)) ,
         leS (<=-trans (<=-cong-+ sizeXY' sizet~t) (<=-help-3-abcd- {a = size~↓! X} {b = size~↓! Y}))
  
    trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (cast-Π {B = B} x X x₁ x₂ x₃) (cast-Π {B' = B'} x₄ Y x₅ x₆ x₇) (leS e) =
      let K , wK , XY- , [U] , [U]' , sizeXY = trans~↓! {n = n} PE.refl (symConEq Γ≡Δ) Y X (<<-trans (<=-help-b'c'- {a = sizeConv↑Term x} {b = sizeConv↑Term x₄} ) e)
          eqU = U≡A-whnf [U] wK
          XY = stability~↓! (symConEq Γ≡Δ) XY-
          XY' = PE.subst (λ X → Γ ⊢ B' ~ B ↓! X ^ ι ¹) eqU XY
          sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ B' ~ B ↓! X ^ ι ¹) size~↓! XY eqU))
                    (<=-trans (≡-to-<= (stabilitySize~↓! (symConEq Γ≡Δ) XY-)) (<=-trans sizeXY (≡-to-<= (+-sym (size~↓! Y) _))))
          X≡Y = soundness~↓! XY'
          Y≡Y = univ (soundnessConv↑Term x₄)
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (stabilityEq (symConEq Γ≡Δ) (trans [U] [U]')) x x₄ (<<-trans (<=-help-id-cong {a = sizeConv↑Term x} {b = sizeConv↑Term x₄}) e)
          Y≡Z = univ (soundnessConv↑Term t~t)
          u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (trans Y≡Z (sym (stabilityEq (symConEq Γ≡Δ) Y≡Y))) x₁ x₅ (<<-trans (<=-help-b''c'' {a = sizeConv↑Term x} {b = sizeConv↑Term x₄}) e) 
          A₁≡B = trans (sym (soundness~↓! (stability~↓! (symConEq Γ≡Δ) Y))) X≡Y
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
      in _ , cast-Π t~t XY' u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (proj₂ (proj₂ (syntacticEqTerm A₁≡B)))) , sym (univ A₁≡B) ,
         leS (<=-trans (<=-cong-+3 sizet~t sizeXY' sizeu~u)
             (<=-help-id-cong' {a = sizeConv↑Term x})) 
  
    trans~↑! {n = 1+ n} el Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) (leS e) =
      let Y≡Y = univ (soundnessConv↑Term x₄)
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄
                                         (<<-trans (<=-help-ab' {a = sizeConv↑Term x} {b = sizeConv↑Term x₄}) e)
          Y≡Z = univ (soundnessConv↑Term t~t)
          u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (trans Y≡Z (sym (stabilityEq (symConEq Γ≡Δ) Y≡Y))) x₁ x₅
                                         (<<-trans (<=-help-ab'' {a = sizeConv↑Term x} {c = sizeConv↑Term x₄}) e)
      in _ , cast-Πℕ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (ℕⱼ  ⊢Γ)) , refl (univ (ℕⱼ  ⊢Γ)) ,
          leS (<=-trans (<=-cong-+ sizet~t sizeu~u) (<=-help-3-abcd {a = sizeConv↑Term x}))
  
    trans~↑! {n = 1+ n} el Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) (leS e) =
      let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl (symConEq Γ≡Δ) (refl (Ugenⱼ ⊢Δ)) x₄ x 
                                         (<<bind-suc <=-help-ab'- e)
          u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x₁ x₅
                                         (<<-trans (<=-help-ab'' {a = sizeConv↑Term x} {c = sizeConv↑Term x₄}) e)
          Π≡Π = univ (soundnessConv↑Term x)
      in _ , cast-ℕΠ (stabilityConv↑Term (symConEq Γ≡Δ) t~t) u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (proj₂ (syntacticEq Π≡Π)) , sym Π≡Π ,
         leS (<=-trans (<=-cong-+ (<=-trans (≡-to-<= (stabilitySizeConv↑Term (symConEq Γ≡Δ) t~t)) sizet~t) sizeu~u) (<=-help-3-abcd- {a = sizeConv↑Term x} {b = sizeConv↑Term x₄}))
  
    trans~↑! {n = 1+ n} el Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) (leS e) =
      let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
          A~A , sizeA~A = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅ (<<-trans (<=-help-id-cong {a = sizeConv↑Term x} {b = sizeConv↑Term x₅}) e)
          B~B , sizeB~B = transConv↑Term {n = n} PE.refl (symConEq Γ≡Δ) (refl (Ugenⱼ ⊢Δ)) x₆ x₁ (<<-trans (<=-help-b'c'- {a = sizeConv↑Term x} {b = sizeConv↑Term x₅}) e)
          u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇ (<<-trans (<=-help-b''c'' {a = sizeConv↑Term x} {b = sizeConv↑Term x₅}) e)
          Π≡Π = trans (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) B~B)))) (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆)))
      in _ , cast-ΠΠ%! A~A (stabilityConv↑Term (symConEq Γ≡Δ) B~B) u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
         refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π ,
         leS (<=-trans (<=-cong-+3 sizeA~A (<=-trans (≡-to-<= (stabilitySizeConv↑Term (symConEq Γ≡Δ) B~B)) sizeB~B) sizeu~u) (<=-help-id-cong'' {a = sizeConv↑Term x}))
   
    trans~↑! {n = 1+ n} el Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) (leS e) =
      let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
          A~A , sizeA~A = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅ (<<-trans (<=-help-id-cong {a = sizeConv↑Term x} {b = sizeConv↑Term x₅}) e)
          B~B , sizeB~B = transConv↑Term {n = n} PE.refl (symConEq Γ≡Δ) (refl (Ugenⱼ ⊢Δ)) x₆ x₁ (<<-trans (<=-help-b'c'- {a = sizeConv↑Term x} {b = sizeConv↑Term x₅}) e)
          u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇ (<<-trans (<=-help-b''c'' {a = sizeConv↑Term x} {b = sizeConv↑Term x₅}) e)
          Π≡Π = trans (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) B~B)))) (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆)))
      in _ , cast-ΠΠ!% A~A (stabilityConv↑Term (symConEq Γ≡Δ) B~B) u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
         refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π ,
         leS (<=-trans (<=-cong-+3 sizeA~A (<=-trans (≡-to-<= (stabilitySizeConv↑Term (symConEq Γ≡Δ) B~B)) sizeB~B) sizeu~u) (<=-help-id-cong'' {a = sizeConv↑Term x}))
  
    trans~↑! {n = 1+ n} PE.refl Γ≡Δ t~u (cast-refl' A~B c x₄) (leS e)
      with neIns (proj₂ (proj₂ (ne~↓! A~B))) c
    ... | isNeIns x' x₁' x₂' ([~] K D whK u~v) =
      let net , neu = ne~↑! t~u
          t≡u = soundness~↑! t~u
          _ , neB , neA = ne~↓! A~B
          ⊢A , ⊢t , ⊢u = syntacticEqTerm t≡u
          _ , A≡B = neTypeEq neu ⊢u (stabilityTerm (symConEq Γ≡Δ) x')
          _ , ⊢B = syntacticEq A≡B
          C , t~v' , A≡C , C≡B  , sizet~v' = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v (<=-trans (<=-help-abc {b = size~↓! A~B}) e)
          _ , ⊢C = syntacticEq A≡C
          XC , wXC , DXC = whNorm ⊢C
          t[conv↑]v = ne-ins (conv ⊢t A≡B) (stabilityTerm (symConEq Γ≡Δ) x₁') neA ([~] _ (red DXC) wXC t~v')
     in _ , cast-refl' (stability~↓! (symConEq Γ≡Δ) A~B) t[conv↑]v (stabilityTerm (symConEq Γ≡Δ) x₄) ,
        A≡B , refl ⊢B ,
        <=-trans (<=-cong-+ (leS (≡-to-<= (stabilitySize~↓! (symConEq Γ≡Δ) A~B))) (leS (leS sizet~v')))
                 <=-help-2-2 
  
    trans~↑! {n = 1+ n} PE.refl Γ≡Δ (cast-refl A~B c x₄) u~v (leS e)
      with neIns (proj₁ (proj₂ (ne~↓! A~B))) c
    ... | isNeIns x' x₁' x₂' ([~] K D whK t~u) =
      let neu , nev = ne~↑! u~v
          u≡v = soundness~↑! u~v
          _ , neA , neB = ne~↓! A~B
          ⊢B , ⊢u , ⊢v = syntacticEqTerm u≡v
          _ , A≡B = neTypeEq neu x₁' (stabilityTerm (symConEq Γ≡Δ) ⊢u)
          A≡B' = univ (soundness~↓! A~B)
          _ , ⊢A' = syntacticEq A≡B'
          C , t~v' , A≡C , C≡B  , sizet~v' = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v (<=-trans (<=-help-abc' {b = size~↓! A~B}) e)
          _ , ⊢C = syntacticEq A≡C
          XC , wXC , DXC = whNorm ⊢C
          t[conv↑]v = ne-ins x' (conv (stabilityTerm (symConEq Γ≡Δ) ⊢v) (sym A≡B)) neA ([~] _ (red DXC) wXC t~v')
      in _ , cast-refl A~B t[conv↑]v x₄ ,
         refl ⊢A' , trans (sym A≡B') A≡B ,
         <=-trans (<=-cong-+ (le-refl (1+ (size~↓! A~B))) (leS (leS sizet~v')))
                  <=-help-2-2'
  
    trans~↑! {n = 1+ n} PE.refl Γ≡Δ t~u (castℕ-refl' ([~] A D whnfB u~v) x₃) (leS e) =
      let net , neu = ne~↑! t~u
          t≡u = soundness~↑! t~u
          ⊢A , ⊢t , ⊢u' = syntacticEqTerm t≡u
          C , t~v , A≡C , C≡B , sizet~v = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v (<=-trans <=-help-1-2 e)
          _ , ⊢C = syntacticEq A≡C 
          X , wX , DX = whNorm ⊢C
          eqℕ = ℕ≡A (trans (sym (subset* D)) (trans (stabilityEq Γ≡Δ (sym C≡B)) (stabilityEq Γ≡Δ (subset* (red DX))))) wX
          DN =  PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqℕ (red DX)
          A≡ℕ = trans A≡C (trans C≡B (stabilityEq (symConEq Γ≡Δ) (subset* D)))
      in _ , castℕ-refl' ([~] _ DN ℕₙ t~v) (stabilityTerm (symConEq Γ≡Δ) x₃) , A≡ℕ , refl (proj₁ (syntacticEq (sym A≡ℕ))) ,
         <=-trans (leS (leS sizet~v)) <=-help-2
  
    trans~↑! {n = 1+ n} PE.refl Γ≡Δ (castℕ-refl ([~] A D whnfB t~u) x₃) u~v (leS e) =
      let neu , nev = ne~↑! u~v
          u≡v = soundness~↑! u~v
          ⊢B , ⊢u , ⊢v = syntacticEqTerm u≡v
          C , t~v , A≡C , C≡B , sizet~v = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v (<=-trans (leS (le-suc (le-refl _))) e)
          _ , ⊢C = syntacticEq A≡C 
          X , wX , DX = whNorm ⊢C
          eqℕ = ℕ≡A (trans (sym (subset* D)) (trans A≡C (subset* (red DX)))) wX 
          DN =  PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqℕ (red DX)
          A≡ℕ = trans (sym (subset* D)) (trans A≡C C≡B)
      in _ , castℕ-refl ([~] _ DN ℕₙ t~v) x₃  , refl (proj₁ (syntacticEq A≡ℕ)) , A≡ℕ ,
         leS (leS sizet~v)
  
    trans~↑! {n = 1+ n} PE.refl Γ≡Δ t~u (castInd-refl' ([~] A D whnfB u~v) x₃) (leS e) =
      let net , neu = ne~↑! t~u
          t≡u = soundness~↑! t~u
          ⊢A , ⊢t , ⊢u' = syntacticEqTerm t≡u
          C , t~v , A≡C , C≡B , sizet~v = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v (<=-trans <=-help-1-2 e)
          _ , ⊢C = syntacticEq A≡C
          X , wX , DX = whNorm ⊢C
          eqInd = Ind≡A (trans (sym (subset* D)) (trans (stabilityEq Γ≡Δ (sym C≡B)) (stabilityEq Γ≡Δ (subset* (red DX))))) wX
          DN =  PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqInd (red DX)
          A≡Ind = trans A≡C (trans C≡B (stabilityEq (symConEq Γ≡Δ) (subset* D)))
      in _ , castInd-refl' ([~] _ DN Indₙ t~v) (stabilityTerm (symConEq Γ≡Δ) x₃) , A≡Ind , refl (proj₁ (syntacticEq (sym A≡Ind))) ,
         <=-trans (leS (leS sizet~v)) <=-help-2

    trans~↑! {n = 1+ n} PE.refl Γ≡Δ (castInd-refl ([~] A D whnfB t~u) x₃) u~v (leS e) =
      let neu , nev = ne~↑! u~v
          u≡v = soundness~↑! u~v
          ⊢B , ⊢u , ⊢v = syntacticEqTerm u≡v
          C , t~v , A≡C , C≡B , sizet~v = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v (<=-trans (leS (le-suc (le-refl _))) e)
          _ , ⊢C = syntacticEq A≡C
          X , wX , DX = whNorm ⊢C
          eqInd = Ind≡A (trans (sym (subset* D)) (trans A≡C (subset* (red DX)))) wX
          DN =  PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqInd (red DX)
          A≡Ind = trans (sym (subset* D)) (trans A≡C C≡B)
      in _ , castInd-refl ([~] _ DN Indₙ t~v) x₃  , refl (proj₁ (syntacticEq A≡Ind)) , A≡Ind ,
         leS (leS sizet~v)

    trans~↑! {n = 1+ n} {A = A} {Γ = Γ} el Γ≡Δ (cast-cong {A'} x x₁ x₄' x₅ x₆) (cast-refl A~B x₃ x₄) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~v , sizet~v = transConv↓Term {n = n} Γ≡Δ (univ (soundness~↓! x)) PE.refl x₄' x₃ (<<-trans (<=-help-b''c'' {a = size~↓! x} {b = 0} {c' = size~↓! A~B}) e)
          K , wK , XY , [U] , _ , sizeXY = trans~↓! {n = n}  PE.refl Γ≡Δ x A~B (<<-trans (<=-help-id-cong-c'' {a = size~↓! x} {b = size~↓! A~B}) e)
          K'' , wK'' , A~A , [U]'' , _ , sizeA~A = trans~↓! {n = n}  PE.refl (reflConEq ⊢Γ) XY x₁
                                                            (<<-trans (<=-cong-+ sizeXY (le-refl _))
                                                            (<<-trans (<=-help-abb'-c'' {a = size~↓! x} {b = size~↓! A~B} ) e))
          eqU'' = U≡A-whnf (trans [U] [U]'' ) wK''
          A~A' = PE.subst (λ X → Γ ⊢ A' ~ A ↓! X ^ ι ¹) eqU'' A~A
          sizeA~A' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ A' ~ A ↓! X ^ ι ¹) size~↓! A~A eqU'')) sizeA~A
      in _ , cast-refl A~A' t~v x₅ ,
         refl (proj₂ (syntacticEq (univ (soundness~↓! A~A')))) , sym (univ (soundness~↓! x₁)) ,
         <=-trans (<=-cong-+ (leS sizeA~A') sizet~v) (leS (<=-trans (<=-cong-+3 sizeXY (le-refl _) (le-refl _)) (<=-help-3-abcde' {a = size~↓! x} {d = size~↓! A~B})))
  
    trans~↑! {n = 1+ n} {A = A} {Δ = Δ} el Γ≡Δ (cast-refl' {B = B} B~A x₃ x₄) (cast-cong {A' = A'} {B' = B'} x₅ x₆ x₉ x₁₀ x₁₁) (leS e) =
      let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
          _ , _ , ⊢A , _ = inversion-Id (un-univ (syntacticTerm x₄))
          _ , erl , _ = inversion-U (un-univ (syntacticTerm ⊢A))
          _ , enextl = typeinfo-PE-injectivity erl
          el = next-inj enextl
          t~v , sizet~v = transConv↓Term {n = n} Γ≡Δ (refl (univ (PE.subst (λ l → _ ⊢ _ ∷ Univ ! ⁰ ^ [ ! , ι l ]) el ⊢A))) PE.refl x₃ x₉
                               (<<-trans (<<cong-right {b = 1+ (size~↓! x₅ + size~↓! x₆)} ) (<<rem-suc e)) 
          K , wK , B~A' , [U] , _  = trans~↓! {n = n} PE.refl Γ≡Δ B~A x₅
                                              (<<bind-suc (<=-help-3-ab {c = sizeConv↓Term x₃}) e) 
          K'' , wK'' , B'~A , [U]'' , _ , sizeB~A  = trans~↓! {n = n} PE.refl (symConEq Γ≡Δ) x₆ B~A
                                                    (<<bind-suc (<=-help-3-ab' {b = size~↓! x₅}) e)
          K' , wK' , B'~A' , [U]' , [U]''' , sizeB~A'  = trans~↓! {n = n} PE.refl (reflConEq ⊢Δ) B'~A x₅
                                                           (<<-trans (<=-cong-+ sizeB~A (le-refl _))
                                                                     (<<-trans (<=-help-3-abb' {a = size~↓! B~A} {b = size~↓! x₅}) e))
          eqU' =  U≡A-whnf (sym [U]''') wK'
          A~A' = stability~↓! (symConEq Γ≡Δ) (PE.subst (λ X →  Δ ⊢ B' ~ A' ↓! X ^ ι ¹) eqU' B'~A')
          _ , neA , neA' = ne~↓! x₅
          A≡A' = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! x₅))
          eqU = U≡A-whnf [U] wK
          B~A'U = PE.subst (λ X →  _ ⊢ B ~ A' ↓! X ^ ι ¹) eqU B~A'
          sizeB~A' = <=inv-suc sizeB~A'
      in _ , cast-refl' A~A' (convConv↓Term (reflConEq ⊢Γ) A≡A' (ne neA') t~v) (stabilityTerm (symConEq Γ≡Δ) x₁₁) ,
        A≡A' ,  sym (univ (soundness~↓! B~A'U)) ,
        PE.subst₂ (λ X Y → 1+ (X + Y) <= (size~↑! (cast-refl' B~A x₃ x₄) + size~↑! (cast-cong x₅ x₆ x₉ x₁₀ x₁₁)))
                  (PE.sym (PE.trans (stabilitySize~↓! (symConEq Γ≡Δ) (PE.subst (λ X →  Δ ⊢ B' ~ A' ↓! X ^ ι ¹) eqU' B'~A'))
                                    (sizeSubst-gen (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓!  B'~A' eqU')))
                  (PE.sym (convConv↓TermSize (reflConEq ⊢Γ) A≡A' (ne neA') t~v))
                  (leS (leS (<=-trans (<=-cong-+ (<=-trans sizeB~A' (<=-cong-+ (<=inv-suc sizeB~A) (le-refl _))) sizet~v)
                       (<=inv-suc (<=-help-3-abcde {b = size~↓! B~A} {c = size~↓! x₅})))))
  
    trans~↑! {n = 1+ n} el Γ≡Δ (cast-refl' x c x₄) (cast-refl x₅ c' x₉) (leS e)
      with neIns (proj₂ (proj₂ (ne~↓! x))) c | neIns (proj₁ (proj₂ (ne~↓! x₅))) c'
    ... | isNeIns x₃ x₁₀ x₁₁ ([~] A D whnfB t~u) | isNeIns x₈ x₁₃ x₁₄ ([~] A' D' whnfB' u~v) =
      let X , t~v , A≡X , X≡B , sizet~v = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v (<<-trans (<=-help-22-rem {a = size~↓! x} {c = 1+ (size~↓! x₅)}) e)
          _ , neu = ne~↑! t~u
          _ , _ , ⊢u = syntacticEqTerm (soundness~↑! t~u)
          _ , ⊢u' , _ = syntacticEqTerm (soundness~↑! u~v)
          _ , A₁≡A = neTypeEq neu (stabilityTerm (symConEq Γ≡Δ) x₈) ⊢u
          _ , A₁≡A' = neTypeEq neu (stabilityTerm (symConEq Γ≡Δ) x₈) (stabilityTerm (symConEq Γ≡Δ) ⊢u')
      in _ , t~v , trans A₁≡A A≡X , trans X≡B (trans (sym A₁≡A') (sym (univ (soundness~↓! x)))) ,
         <=-trans sizet~v (<=-help-22-rem {a = 1+ (size~↓! x)} {c = 1+ (size~↓! x₅)})
  
    trans~↑! {n = 1+ n} el Γ≡Δ (castℕ-refl' x x₁) (castℕ-refl x₂ x₃) (leS e) =
      let X , wX , t~t , ℕ≡X , X≡ℕ , sizet~t = trans~↓! {n = n} PE.refl Γ≡Δ x x₂ (<<-trans (<=-help-ab1' {a = size~↓! x}) e)
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          eqℕ = ℕ≡A ℕ≡X wX
          t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
          [~] K D wK t~t'' = t~t'
          sizet~t' = <=-trans (≡-to-<= (sizeSubst-gen (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓! t~t eqℕ)) sizet~t
      in _ , t~t'' , sym (subset* D) , subset* D ,
         <=-trans (<=inv-suc sizet~t') <=-help-2-1
  
    trans~↑! {n = 1+ n} el Γ≡Δ (castInd-refl' x x₁) (castInd-refl x₂ x₃) (leS e) =
      let X , wX , t~t , Ind≡X , X≡Ind , sizet~t = trans~↓! {n = n} PE.refl Γ≡Δ x x₂ (<<-trans (<=-help-ab1' {a = size~↓! x}) e)
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          eqInd = Ind≡A Ind≡X wX
          t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqInd t~t
          [~] K D wK t~t'' = t~t'
          sizet~t' = <=-trans (≡-to-<= (sizeSubst-gen (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓! t~t eqInd)) sizet~t
      in _ , t~t'' , sym (subset* D) , subset* D ,
         <=-trans (<=inv-suc sizet~t') <=-help-2-1

    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (cast-neℕ {A = A} x₁ x₂ x₃ x₄) (cast-neℕ {A' = A'} x₅ x₆ x₇ x₈) (leS e) =
      let K , wK , XY , [U] , _ , sizeXY = trans~↓! {n = n} PE.refl Γ≡Δ x₁ x₅ (<<-trans (<=-help-ab' {a = size~↓! x₁} {b = size~↓! x₅} ) e)
          eqU = U≡A-whnf [U] wK
          XY' = PE.subst (λ X → Γ ⊢ A ~ A' ↓! X ^ ι ¹) eqU XY
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ A ~ A' ↓! X ^ ι ¹) size~↓! XY eqU)) sizeXY
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (univ (soundness~↓! x₁)) x₂ x₆ (<<-trans (<=-help-ab'' {a = size~↓! x₁} {c = size~↓! x₅}) e)
      in _ , cast-neℕ XY' t~t x₃ (stabilityTerm (symConEq Γ≡Δ) x₈) , refl (univ (ℕⱼ ⊢Γ)) , refl (univ (ℕⱼ ⊢Γ)) ,
         leS (<=-trans (<=-cong-+ sizeXY' sizet~t) (<=-help-3-abcd {a = size~↓! x₁} {b = size~↓! x₅}))
  
    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (cast-neInd {A = A} x₁ x₂ x₃ x₄) (cast-neInd {A' = A'} x₅ x₆ x₇ x₈) (leS e) =
      let K , wK , XY , [U] , _ , sizeXY = trans~↓! {n = n} PE.refl Γ≡Δ x₁ x₅ (<<-trans (<=-help-ab' {a = size~↓! x₁} {b = size~↓! x₅} ) e)
          eqU = U≡A-whnf [U] wK
          XY' = PE.subst (λ X → Γ ⊢ A ~ A' ↓! X ^ ι ¹) eqU XY
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ A ~ A' ↓! X ^ ι ¹) size~↓! XY eqU)) sizeXY
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (univ (soundness~↓! x₁)) x₂ x₆ (<<-trans (<=-help-ab'' {a = size~↓! x₁} {c = size~↓! x₅}) e)
      in _ , cast-neInd XY' t~t x₃ (stabilityTerm (symConEq Γ≡Δ) x₈) , refl (univ (Indⱼ ⊢Γ)) , refl (univ (Indⱼ ⊢Γ)) ,
         leS (<=-trans (<=-cong-+ sizeXY' sizet~t) (<=-help-3-abcd {a = size~↓! x₁} {b = size~↓! x₅}))

    trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (cast-Ind {A = A} X x x₁ x₂) (cast-Ind {A' = A'} Y x₃ x₄ x₅) (leS e) =
      let K , wK , XY- , [U] , _ , sizeXY = trans~↓! {n = n} PE.refl (symConEq Γ≡Δ) Y X (<<bind-suc <=-help-ab'- e)
          eqU = U≡A-whnf [U] wK
          XY = stability~↓! (symConEq Γ≡Δ) XY-
          XY' = PE.subst (λ X →  Γ ⊢ A' ~ A ↓! X ^ ι ¹) eqU XY
          ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (Indⱼ ⊢Γ))) x x₃ (<<-trans (<=-help-ab'' {a = size~↓! X} {c = size~↓! Y}) e)
          sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X →  Γ ⊢ A' ~ A ↓! X ^ ι ¹) size~↓! XY eqU)) (<=-trans (≡-to-<= (stabilitySize~↓! (symConEq Γ≡Δ) XY-)) sizeXY)
      in _ , cast-Ind XY' t~t x₁ (stabilityTerm (symConEq Γ≡Δ) x₅) , refl (proj₂ (syntacticEq (univ (soundness~↓! X)))) , sym (univ (soundness~↓! X)) ,
         leS (<=-trans (<=-cong-+ sizeXY' sizet~t) (<=-help-3-abcd- {a = size~↓! X} {b = size~↓! Y}))

    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (cast-Indℕ x x₁ x₂) (cast-Indℕ x₃ x₄ x₅) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (Indⱼ ⊢Γ))) x x₃ (<<-trans (<=-help-ab1' {a = sizeConv↑Term x}) e)
      in _ , cast-Indℕ t~t x₁ (stabilityTerm (symConEq Γ≡Δ) x₅) , refl (univ (ℕⱼ ⊢Γ)) , refl (univ (ℕⱼ ⊢Γ)) ,
         <=-trans (leS sizet~t) (<=-help-rigid1 {a = sizeConv↑Term x} {b = sizeConv↑Term x₃})

    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (cast-ℕInd x x₁ x₂) (cast-ℕInd x₃ x₄ x₅) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (ℕⱼ ⊢Γ))) x x₃ (<<-trans (<=-help-ab1' {a = sizeConv↑Term x}) e)
      in _ , cast-ℕInd t~t x₁ (stabilityTerm (symConEq Γ≡Δ) x₅) , refl (univ (Indⱼ ⊢Γ)) , refl (univ (Indⱼ ⊢Γ)) ,
         <=-trans (leS sizet~t) (<=-help-rigid1 {a = sizeConv↑Term x} {b = sizeConv↑Term x₃})

    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (cast-IndInd x₀ x₁ x₂ x₃) (cast-IndInd x₄ x₅ x₆ x₇) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (Indⱼ ⊢Γ))) x₁ x₅ (<<-trans (<=-help-ab1' {a = sizeConv↑Term x₁}) e)
      in _ , cast-IndInd x₀ t~t x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (Indⱼ ⊢Γ)) , refl (univ (Indⱼ ⊢Γ)) ,
         <=-trans (leS sizet~t) (<=-help-rigid1 {a = sizeConv↑Term x₁} {b = sizeConv↑Term x₅})

    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (cast-IndΠ x x₁ x₂ x₃) (cast-IndΠ x₄ x₅ x₆ x₇) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄
                                         (<<-trans (<=-help-ab' {a = sizeConv↑Term x} {b = sizeConv↑Term x₄}) e)
          u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (Indⱼ ⊢Γ))) x₁ x₅
                                         (<<-trans (<=-help-ab'' {a = sizeConv↑Term x} {c = sizeConv↑Term x₄}) e)
          A₁≡B = univ (soundnessConv↑Term x)
      in _ , cast-IndΠ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (proj₁ (syntacticEq A₁≡B)) , A₁≡B ,
         leS (<=-trans (<=-cong-+ sizet~t sizeu~u) (<=-help-3-abcd {a = sizeConv↑Term x}))

    trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (cast-ΠInd x x₁ x₂ x₃) (cast-ΠInd x₄ x₅ x₆ x₇) (leS e) =
      let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
          t~t , sizet~t = transConv↑Term {n = n} PE.refl (symConEq Γ≡Δ) (refl (Ugenⱼ ⊢Δ)) x₄ x
                                         (<<bind-suc <=-help-ab'- e)
          u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (sym (univ (soundnessConv↑Term x))) x₁ x₅
                                         (<<-trans (<=-help-ab'' {a = sizeConv↑Term x} {c = sizeConv↑Term x₄}) e)
      in _ , cast-ΠInd (stabilityConv↑Term (symConEq Γ≡Δ) t~t) u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (Indⱼ ⊢Γ)) , refl (univ (Indⱼ ⊢Γ)) ,
         leS (<=-trans (<=-cong-+ (<=-trans (≡-to-<= (stabilitySizeConv↑Term (symConEq Γ≡Δ) t~t)) sizet~t) sizeu~u) (<=-help-3-abcd- {a = sizeConv↑Term x} {b = sizeConv↑Term x₄}))

    trans~↑! {n = 1+ n} el Γ≡Δ (castInd-refl' x₂ x₃) (cast-IndInd x₄ x₅ x₆ x₇) (leS e) = ⊥-elim (x₄ PE.refl)

    trans~↑! {n = 1+ n} el Γ≡Δ (cast-IndInd x₂ x₃ x₄ x₅) (castInd-refl x₆ x₇) (leS e) = ⊥-elim (x₂ PE.refl)

    trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (cast-neΠ {B = B} x₁ x₂ x₃ x₄ x₅) (cast-neΠ {B' = B'} x₆ x₇ x₈ x₉ x₁₀) (leS e) =
      let K , wK , XY , [U] , _ , sizeXY = trans~↓! {n = n} PE.refl Γ≡Δ x₂ x₇ (<<-trans (<=-help-b'c' {a = sizeConv↑Term x₁} {b = sizeConv↑Term x₆}) e)
          eqU = U≡A-whnf [U] wK
          XY' = PE.subst (λ X → Γ ⊢ B ~ B' ↓! X ^ ι ¹) eqU XY
          sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ B ~ B' ↓! X ^ ι ¹) size~↓! XY eqU)) sizeXY
          ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
          Π~Π , sizeΠ~Π = transConv↑Term {n = n} PE.refl (symConEq Γ≡Δ) (refl (Ugenⱼ ⊢Δ)) x₆ x₁ (<<-trans (<=-help-id-cong- {a = sizeConv↑Term x₁} {b = sizeConv↑Term x₆}) e)
          t~t , sizet~t = transConv↑Term {n = n} PE.refl Γ≡Δ (univ (soundness~↓! x₂)) x₃ x₈ (<<-trans (<=-help-b''c'' {a = sizeConv↑Term x₁} {b = sizeConv↑Term x₆}) e)
          Π≡Π = sym (soundnessConv↑Term x₁)
          sizeΠ~Π' = <=-trans (≡-to-<= (stabilitySizeConv↑Term (symConEq Γ≡Δ) Π~Π)) sizeΠ~Π
      in _ , cast-neΠ (stabilityConv↑Term (symConEq Γ≡Δ) Π~Π) XY' t~t x₄ (stabilityTerm (symConEq Γ≡Δ) x₁₀) , refl (univ (proj₁ (proj₂ (syntacticEqTerm Π≡Π)))) , univ Π≡Π ,
        leS (<=-trans (<=-cong-+3 sizeΠ~Π' sizeXY' sizet~t) (<=-help-id-cong'- {a = sizeConv↑Term x₁} {b = sizeConv↑Term x₆}))
  
    -- Impossible pairs: the two derivations disagree on the head of a type in
    -- the middle cast, which would force a ↓! endpoint to be ℕ, Π or Ind even
    -- though ↓! only relates neutrals.  Written out because letting the
    -- coverage checker find them costs an emptiness search per pair.
    trans~↑! _ _ (cast-cong f _ _ _ _) (castℕ-refl _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-cong _ f _ _ _) (cast-neℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-ℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-cong _ f _ _ _) (cast-neΠ _ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-Π _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-cong _ f _ _ _) (cast-Πℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-ℕΠ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-ΠΠ%! _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-ΠΠ!% _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-cong _ f _ _ _) (cast-neInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-Ind _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (castInd-refl _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-IndΠ _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-cong _ f _ _ _) (cast-ΠInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-cong _ f _ _ _) (cast-Indℕ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-ℕInd _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-cong f _ _ _ _) (cast-IndInd _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (castℕ-refl _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-neℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-ℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-neΠ _ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-Π _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-Πℕ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-ℕΠ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-ΠΠ%! _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-ΠΠ!% _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-neInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-Ind _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (castInd-refl _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-IndΠ _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-ΠInd _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-Indℕ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-ℕInd _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-refl' f _ _) (cast-IndInd _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (castℕ-refl' _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (castℕ-refl' _ _) (cast-refl f _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (castℕ-refl' _ _) (cast-neℕ f _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (castℕ-refl' _ _) (cast-ℕ f _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neℕ _ _ _ _) (cast-cong _ f _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neℕ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neℕ f _ _ _) (castℕ-refl _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neℕ f _ _ _) (cast-ℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neℕ f _ _ _) (cast-Π _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neℕ f _ _ _) (cast-Πℕ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neℕ f _ _ _) (cast-Ind _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-neℕ f _ _ _) (cast-Indℕ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-ℕ _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕ f _ _ _) (castℕ-refl _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕ f _ _ _) (cast-neℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕ f _ _ _) (cast-neΠ _ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ℕ f _ _ _) (cast-ℕΠ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ℕ f _ _ _) (cast-neInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-ℕ f _ _ _) (cast-ℕInd _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-neΠ _ _ _ _ _) (cast-cong _ f _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neΠ _ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neΠ _ f _ _ _) (cast-ℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neΠ _ f _ _ _) (cast-Π _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neΠ _ f _ _ _) (cast-ℕΠ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neΠ _ f _ _ _) (cast-ΠΠ%! _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neΠ _ f _ _ _) (cast-ΠΠ!% _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neΠ _ f _ _ _) (cast-Ind _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-neΠ _ f _ _ _) (cast-IndΠ _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-Π _ _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Π _ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Π _ f _ _ _) (cast-neℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-Π _ f _ _ _) (cast-neΠ _ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Π _ f _ _ _) (cast-Πℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-Π _ f _ _ _) (cast-ΠΠ%! _ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Π _ f _ _ _) (cast-ΠΠ!% _ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Π _ f _ _ _) (cast-neInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Π _ f _ _ _) (cast-ΠInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Πℕ _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Πℕ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Πℕ _ _ _ _) (cast-neℕ f _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Πℕ _ _ _ _) (cast-Π _ f _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-ℕΠ _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕΠ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕΠ _ _ _ _) (cast-ℕ f _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-ℕΠ _ _ _ _) (cast-neΠ _ f _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ΠΠ%! _ _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠΠ%! _ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠΠ%! _ _ _ _ _) (cast-neΠ _ f _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠΠ%! _ _ _ _ _) (cast-Π _ f _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-ΠΠ!% _ _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠΠ!% _ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠΠ!% _ _ _ _ _) (cast-neΠ _ f _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠΠ!% _ _ _ _ _) (cast-Π _ f _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neInd _ _ _ _) (cast-cong _ f _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-neInd _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-neInd f _ _ _) (cast-ℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neInd f _ _ _) (cast-Π _ _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neInd f _ _ _) (cast-Ind _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-neInd f _ _ _) (castInd-refl _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-neInd f _ _ _) (cast-ΠInd _ _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-neInd f _ _ _) (cast-ℕInd _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-neInd f _ _ _) (cast-IndInd _ _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-Ind _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Ind _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Ind f _ _ _) (cast-neℕ _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-Ind f _ _ _) (cast-neΠ _ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Ind f _ _ _) (cast-neInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Ind f _ _ _) (castInd-refl _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Ind f _ _ _) (cast-IndΠ _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Ind f _ _ _) (cast-Indℕ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-Ind f _ _ _) (cast-IndInd _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (castInd-refl' _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (castInd-refl' _ _) (cast-refl f _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (castInd-refl' _ _) (cast-neInd f _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (castInd-refl' _ _) (cast-Ind f _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-IndΠ _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-IndΠ _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-IndΠ _ _ _ _) (cast-neΠ _ f _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-IndΠ _ _ _ _) (cast-Ind f _ _ _) _ = ⊥-elim (¬neΠ (neʳ f))
    trans~↑! _ _ (cast-ΠInd _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠInd _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-ΠInd _ _ _ _) (cast-Π _ f _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-ΠInd _ _ _ _) (cast-neInd f _ _ _) _ = ⊥-elim (¬neΠ (neˡ f))
    trans~↑! _ _ (cast-Indℕ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Indℕ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Indℕ _ _ _) (cast-neℕ f _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-Indℕ _ _ _) (cast-Ind f _ _ _) _ = ⊥-elim (¬neℕ (neʳ f))
    trans~↑! _ _ (cast-ℕInd _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕInd _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-ℕInd _ _ _) (cast-ℕ f _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
    trans~↑! _ _ (cast-ℕInd _ _ _) (cast-neInd f _ _ _) _ = ⊥-elim (¬neℕ (neˡ f))
    trans~↑! _ _ (cast-IndInd _ _ _ _) (cast-cong f _ _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-IndInd _ _ _ _) (cast-refl f _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-IndInd _ _ _ _) (cast-neInd f _ _ _) _ = ⊥-elim (¬neInd (neˡ f))
    trans~↑! _ _ (cast-IndInd _ _ _ _) (cast-Ind f _ _ _) _ = ⊥-elim (¬neInd (neʳ f))
  
    -- trans~↑! = {!!}
  
    trans~↑% : ∀ {t u v A Γ Δ  l}
           → ⊢ Γ ≡ Δ
           → Γ ⊢ t ~ u ↑% A ^ l
           → Δ ⊢ u ~ v ↑% A ^ l
           → Γ ⊢ t ~ v ↑% A ^ l
    trans~↑% Γ≡Δ (%~↑ ⊢t ⊢u) (%~↑ ⊢u′ ⊢v) =
      let ⊢Δu′ = stabilityTerm (symConEq Γ≡Δ) ⊢u′
          ⊢Δv = stabilityTerm (symConEq Γ≡Δ) ⊢v
      in %~↑ ⊢t ⊢Δv
  
    -- Transitivity of algorithmic equality of neutrals with types in WHNF.
    trans~↓! : ∀ {n t u v A B Γ Δ l l'}
            → l PE.≡ l'
            → ⊢ Γ ≡ Δ
            → (e : Γ ⊢ t ~ u ↓! A ^ l)
            → (e' : Δ ⊢ u ~ v ↓! B ^ l')
            → (size~↓! e + size~↓! e') << n
            → ∃ λ C → Whnf C × ∃ λ (e'' : Γ ⊢ t ~ v ↓! C ^ l) → Γ ⊢ A ≡ C ^ [ ! , l ] × Γ ⊢ C ≡ B ^ [ ! , l ] × size~↓! e'' <= (size~↓! e + size~↓! e')
  
    trans~↓! {n = 0} PE.refl Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) ()
                     
    trans~↓! {n = 1+ n} PE.refl Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) (leS e) =
     let leq = (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
         C , t~v , A≡C , C≡B , size = trans~↑! {n = n} PE.refl Γ≡Δ k~l k~l₁ (<<-trans leq e)
         ⊢C , _ = syntacticEq C≡B
         X , wX , DX = whNorm ⊢C
     in X , wX , [~] _ (red DX) wX t~v , trans (sym (subset* D)) (trans A≡C (subset* (red DX))) , trans (trans (sym (subset* (red DX))) C≡B) (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)) , leS (<=-trans size leq)
  
    -- Transitivity of algorithmic equality of types.
    transConv↑ : ∀ {n A B C r Γ Δ}
              → ⊢ Γ ≡ Δ
              → (e : Γ ⊢ A [conv↑] B ^ r)
              → (e' : Δ ⊢ B [conv↑] C ^ r)
              → (sizeConv↑ e + sizeConv↑ e') << n
              → ∃ λ (e'' : Γ ⊢ A [conv↑] C ^ r) → sizeConv↑ e'' <= (sizeConv↑ e + sizeConv↑ e')
  
    transConv↑ {n = 0} _ _ _ ()
    
    transConv↑ {n = 1+ n} {r = r} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) (leS e) =
      let leq = <=-cong-+ (le-refl _ ) 
                          (le-suc (≡-to-<= (sizeSubst-gen (λ x → _ ⊢ x [conv↓] B″ ^ r)
                                                          sizeConv↓ A′<>B″ (whrDet* (D₁ , whnfA″)
                                                          (stabilityRed* Γ≡Δ D′ , whnfB′)))))
          A<>B , size = transConv↓ {n = n} Γ≡Δ A′<>B′
                                   (PE.subst (λ x → _ ⊢ x [conv↓] B″ ^ r)
                                     (whrDet* (D₁ , whnfA″) (stabilityRed* Γ≡Δ D′ , whnfB′))
                                   A′<>B″) (<<-trans leq e)
      in [↑] A′ B″ D (stabilityRed* (symConEq Γ≡Δ) D″) whnfA′ whnfB″ A<>B ,
         leS (<=-trans size leq)
          
    -- Transitivity of algorithmic equality of types in WHNF.
    transConv↓ : ∀ {n A B C r Γ Δ}
              → ⊢ Γ ≡ Δ
              → (e : Γ ⊢ A [conv↓] B ^ r)
              → (e' : Δ ⊢ B [conv↓] C ^ r)
              → (sizeConv↓ e + sizeConv↓ e') << n
              → ∃ λ (e'' : Γ ⊢ A [conv↓] C ^ r) → sizeConv↓ e'' <= (sizeConv↓ e + sizeConv↓ e')
  
    transConv↓ {n = 0} _ _ _ ()
    
    transConv↓ Γ≡Δ (U-refl e x) (U-refl e₁ x₁) _ = U-refl (PE.trans e e₁) x , leS le0
    transConv↓ {n = 1+ n} Γ≡Δ (univ x) (univ y) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          leq = <=-cong-+ (le-refl _) (le-suc (le-refl _))
          X , size = transConv↓Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ )) PE.refl x y (<<-trans leq e)
      in univ X , leS (<=-trans size leq)
  
    -- Transitivity of algorithmic equality of terms.
    transConv↑Term : ∀ {n t u v A B Γ Δ l l'}
                  → l PE.≡ l'
                  → ⊢ Γ ≡ Δ
                  → Γ ⊢ A ≡ B ^ [ ! , l ]
                  → (e : Γ ⊢ t [conv↑] u ∷ A ^ l)
                  → (e' : Δ ⊢ u [conv↑] v ∷ B ^ l')
                  → (sizeConv↑Term e + sizeConv↑Term e') << n
                  → ∃ λ (e'' : Γ ⊢ t [conv↑] v ∷ A ^ l) → sizeConv↑Term e'' <= (sizeConv↑Term e + sizeConv↑Term e')
    transConv↑Term {n = 0} _ _ _ _ _ ()
    transConv↑Term {n = 1+ n} PE.refl Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₂ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁) (leS e) =
      let B₁≡B₂ = trans (sym (subset* D))
                        (trans A≡B
                               (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))
          d₁″ = conv* (stabilityRed*Term (symConEq Γ≡Δ) d″) (sym B₁≡B₂)
          d₁′  = stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B₂)
          eq = whrDet*Term (d₁ , whnft″) (d₁′ , whnfu′)
          leq = <=-cong-+ (le-refl _) (le-suc (≡-to-<= (sizeSubst-gen (λ x → _ ⊢ x [conv↓] u″ ∷ B₂ ^ _) sizeConv↓Term  t<>u₁ eq)))
          t<>v , sizet<>v = transConv↓Term {n = n} Γ≡Δ B₁≡B₂ PE.refl t<>u
                                           (PE.subst (λ x → _ ⊢ x [conv↓] u″ ∷ B₂ ^ _) eq t<>u₁)
                                           (<<-trans leq e)
      in  [↑]ₜ B₁ t′ u″ D d d₁″ whnfB whnft′ whnfu″ t<>v ,
          leS (<=-trans sizet<>v leq)
  
    -- Transitivity of algorithmic equality of terms in WHNF.
    transConv↓Term : ∀ {n t u v A B Γ Δ l l'}
                  → ⊢ Γ ≡ Δ
                  → Γ ⊢ A ≡ B ^ [ ! , l ]
                  → l PE.≡ l'
                  → (e : Γ ⊢ t [conv↓] u ∷ A ^ l)
                  → (e' : Δ ⊢ u [conv↓] v ∷ B ^ l')
                  → (sizeConv↓Term e + sizeConv↓Term e') << n
                  → ∃ λ (e'' : Γ ⊢ t [conv↓] v ∷ A ^ l) → sizeConv↓Term e'' <= (sizeConv↓Term e + sizeConv↓Term e')
  
    transConv↓Term {n = 0} _ _ _ _ _ () 
  
    transConv↓Term {1+ n} {t} {u} {v} {A} {B} {Γ} {Δ} {l} Γ≡Δ A≡B el (ne x) (ne x₁) (leS e) =
      let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
          C , wC , x~x , A≡C , C≡B , size = trans~↓! {n = n} el Γ≡Δ x x₁ (<<-trans leq e)
          eqU = U≡A-whnf A≡C wC
          x~x' = PE.subst (λ X →  Γ ⊢ t ~ v ↓! X ^ l) eqU x~x
      in ne x~x' , PE.subst (λ X → 1+ X <= 1+ (1+ (size~↑! (_⊢_~_↓!_^_.k~l x) + 1+ (size~↓! x₁))))
                            (PE.sym (sizeSubst-gen (λ X →  Γ ⊢ t ~ v ↓! X ^ l) size~↓! x~x eqU))
                            (leS (<=-trans size leq)) 
    transConv↓Term {1+ n} {t} {u} {v} {A} {B} {Γ} {Δ} {l} Γ≡Δ A≡B el (ℕ-ins x) (ℕ-ins x₁) (leS e) =
      let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
          C , wC , x~x , A≡C , C≡B , size = trans~↓! {n = n}  PE.refl Γ≡Δ x x₁ (<<-trans leq e)
          eqℕ = ℕ≡A A≡C wC
          x~x' = PE.subst (λ X →  Γ ⊢ t ~ v ↓! X ^ l) eqℕ x~x
      in ℕ-ins x~x' , PE.subst (λ X → 1+ X <= 1+ (1+ (size~↑! (_⊢_~_↓!_^_.k~l x) + 1+ (size~↓! x₁))))
                               (PE.sym (sizeSubst-gen (λ X →  Γ ⊢ t ~ v ↓! X ^ l) size~↓! x~x eqℕ))
                               (leS (<=-trans size leq))
    transConv↓Term {1+ n} {t} {u} {v} {A} {B} {Γ} {Δ} {l} Γ≡Δ A≡B el (Ind-ins x) (Ind-ins x₁) (leS e) =
      let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
          C , wC , x~x , A≡C , C≡B , size = trans~↓! {n = n}  PE.refl Γ≡Δ x x₁ (<<-trans leq e)
          eqInd = Ind≡A A≡C wC
          x~x' = PE.subst (λ X →  Γ ⊢ t ~ v ↓! X ^ l) eqInd x~x
      in Ind-ins x~x' , PE.subst (λ X → 1+ X <= 1+ (1+ (size~↑! (_⊢_~_↓!_^_.k~l x) + 1+ (size~↓! x₁))))
                               (PE.sym (sizeSubst-gen (λ X →  Γ ⊢ t ~ v ↓! X ^ l) size~↓! x~x eqInd))
                               (leS (<=-trans size leq))
  
    transConv↓Term {n = 1+ n} {Δ = Δ} Γ≡Δ A≡B el (ne-ins t u x x₁) (ne-ins {k} {l} {M} {N} t′ u′ x₂ x₃) (leS e) =
      let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
          C , wC , x~x , A≡C , C≡B , size = trans~↓! {n = n} el Γ≡Δ x₁ x₃ (<<-trans leq e)
      in ne-ins t (conv (stabilityTerm (symConEq Γ≡Δ) (PE.subst (λ lx → Δ ⊢ l ∷ N ^ [ ! , lx ]) (PE.sym el) u′))
                        (sym A≡B)) x
                x~x ,
         leS (<=-trans size leq)
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (zero-refl x₁) _ =
      zero-refl x , leS (le0)
    transConv↓Term {n = 1+ n} Γ≡Δ A≡B el (suc-cong x) (suc-cong x₁) (leS e) =
      let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
          t~v , size = transConv↑Term {n = n} el Γ≡Δ A≡B x x₁ (<<-trans leq e)
      in suc-cong t~v ,
         leS (<=-trans size leq)
    transConv↓Term {n = 1+ n} {Δ = Δ} Γ≡Δ A≡B el
                   (η-eq {rF = rF₁} l< l<' x x₁ x₂ y y₁ x₃)
                   (η-eq {u} {v} {F} {G} {rF} {lF} {lG} {l} l<'' l<''' x₄ x₅ x₆ y₂ y₃ x₇)
                   (leS e) =
      let F₁≡F , rF₁≡rF , lF₁≡lF , lG₁≡lG , G₁≡G = injectivity (PE.subst (λ lx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° lx ^ _ ^ _) (ιinj (PE.sym el)) A≡B )
          lesubst = sizeSubst₃-gen (λ lx lx' rx → Δ ∙ F ^ [ rx , lx' ] ⊢  wk1 u ∘ var 0 ^ lx [conv↑] wk1 v ∘ var 0 ^ lx ∷ G ^ ι lG)
                                  sizeConv↑Term x₇ (PE.sym (ιinj el)) (PE.sym (PE.cong ι lF₁≡lF)) (PE.sym rF₁≡rF)
          leq = leS (<=-cong-+ (le-refl (sizeConv↓Term (_⊢_[conv↑]_∷_^_.t<>u x₃)))
                               (le-suc (≡-to-<= lesubst)))
          t~v , size = transConv↑Term {n = n} (PE.cong ι lG₁≡lG) (Γ≡Δ ∙ F₁≡F) G₁≡G x₃ 
                                    (PE.subst₃ (λ lx lx' rx → Δ ∙ F ^ [ rx , lx' ] ⊢  wk1 u ∘ var 0 ^ lx [conv↑] wk1 v ∘ var 0 ^ lx ∷ G ^ ι lG)
                                               (PE.sym (ιinj el))
                                               (PE.sym (PE.cong ι lF₁≡lF))
                                               (PE.sym rF₁≡rF) x₇)
                                    (<<-trans leq e)
      in η-eq l< l<' x x₁ (conv (stabilityTerm (symConEq Γ≡Δ)
                                             (PE.subst (λ lx → Δ ⊢ v ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , lx ]) (PE.sym el) x₆))
                              (sym A≡B))
               y y₃ t~v ,
         leS (<=-trans size leq)
    transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ℕ-refl x₁) _ = ℕ-refl x , leS le0
    transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (Empty-refl x₁) _ = Empty-refl x , leS le0
    transConv↓Term Γ≡Δ A≡B el (U-refl e x) (U-refl e₁ x₁) _ = U-refl (PE.trans e e₁) x , leS le0
    transConv↓Term {n = 1+ n} Γ≡Δ A≡B el
                   (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' x₅ x₆ x₇)
                   (Π-cong PE.refl PE.refl PE.refl PE.refl x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          rF≡rF₁ , _ = Uinjectivity A≡B
          F~F , sizeF = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (Ugenⱼ ⊢Γ )) x₆ x₁₄
                                       (<<-trans (leS (<=-help-ab' {b = sizeConv↑Term x₁₄})) e)
          G~G , sizeG = transConv↑Term {n = n} PE.refl (Γ≡Δ ∙ univ (soundnessConv↑Term x₆))
                                (refl (Ugenⱼ (⊢Γ ∙ x₅))) x₇ x₁₅
                                (<<-trans (<=-help-ab'' {a = sizeConv↑Term x₆} {c = sizeConv↑Term x₁₄}) e) 
      in Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' x₅
                F~F
                G~G ,
         leS (<=-trans (<=-cong-+ sizeF sizeG) (leS (<=-help-3-abcd {b = sizeConv↑Term x₁₄} {c = sizeConv↑Term x₇}))) 
   
    transConv↓Term {n = 1+ n} {Γ = Γ} Γ≡Δ A≡B el (Id-cong {l = l} {A = A} X x x₁) (Id-cong {A' = A'} Y x₂ x₃) (leS e) =
      let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
          rF≡rF₁ , _ = Uinjectivity A≡B
          _ , _ , [A'] = (syntacticEqTerm (soundnessConv↑Term X))
          [A']Δ = stabilityTerm Γ≡Δ [A']
          _ , [A']Δ' , _ = syntacticEqTerm (soundnessConv↑Term Y)
          _ , el' = relevance-unicity (univ [A']Δ) (univ [A']Δ')
          el = PE.cong next (ιinj el')
          XY' , sizeXY = transConv↑Term {n = n} el Γ≡Δ (PE.subst (λ X →  Γ ⊢ U l ≡ U X ^ [ ! , next l ]) (ιinj el') (refl (Ugenⱼ ⊢Γ))) X Y
                                       (<<-trans (leS (<=-help-id-cong {b = sizeConv↑Term Y})) e)
          X≡Y = univ (soundnessConv↑Term XY')
          Y≡Y = PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ ! , ι lx ]) (PE.sym (next-inj el)) (univ (soundnessConv↑Term Y))
          t~t , sizet~t = transConv↑Term {n = n} el' Γ≡Δ
                                         (trans X≡Y (stabilityEq (symConEq Γ≡Δ) (sym Y≡Y))) x x₂
                                         (<<-trans (<=-help-b'c' {a = sizeConv↑Term X} {b = sizeConv↑Term Y}) e)
          u~u , sizeu~u = transConv↑Term {n = n} el' Γ≡Δ (trans X≡Y (stabilityEq (symConEq Γ≡Δ) (sym Y≡Y))) x₁ x₃ 
                                         (<<-trans (<=-help-b''c'' {a = sizeConv↑Term X} {b = sizeConv↑Term Y}) e)
      in Id-cong XY' t~t u~u , 
         leS (<=-trans (<=-cong-+3 sizeXY sizet~t sizeu~u) 
             (<=-help-id-cong' {a = sizeConv↑Term X}))                                    
  
    transConv↓Term Γ≡Δ A≡B PE.refl (ℕ-refl x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.U≢Π! A≡B)
    transConv↓Term {Γ = Γ} Γ≡Δ A≡B el (Empty-refl x) (η-eq {F = F} {G = G} {rF = rF} {lF = lF} {lG = lG} {l = l} x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
      let X = PE.subst (λ lx → Γ ⊢ SProp ≡  Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , lx ]) el A≡B
      in ⊥-elim (WF.U≢Π! X)
    transConv↓Term Γ≡Δ A≡B el (Π-cong {rΠ = rΠ} {lΠ = lΠ} x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₀) (η-eq x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) =
      let X = PE.subst (λ lx → _ ⊢ Univ rΠ lΠ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ _ ^ [ _ , lx ]) el A≡B
      in ⊥-elim (WF.U≢Π! X)
    transConv↓Term {Γ = Γ} Γ≡Δ A≡B el (Id-cong x₆ x₇ x₀) (η-eq {F = F} {G = G} {rF = rF} {lF = lF} {lG = lG} {l = l} x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) =
      let X = PE.subst (λ lx → Γ ⊢ SProp ≡ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , lx ]) el A≡B
      in ⊥-elim (WF.U≢Π! X)
  
    transConv↓Term Γ≡Δ A≡B el (ne x) (ℕ-ins x₁) = ⊥-elim (WF.U≢ℕ! A≡B)
    transConv↓Term Γ≡Δ A≡B PE.refl (ne x) (ne-ins x₁ x₂ x₃ x₄) = ⊥-elim (WF.U≢ne! x₃ A≡B)
    transConv↓Term Γ≡Δ A≡B PE.refl (ne x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.U≢Π! A≡B)
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (ne-ins t u x₂ x₃) = ⊥-elim (WF.ℕ≢ne! x₂ A≡B)
    transConv↓Term Γ≡Δ A≡B PE.refl (ℕ-ins x) (η-eq _ _ x₂ x₃ x₄ y y₁ x₅) = ⊥-elim (WF.ℕ≢Π! A≡B)
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (ne x₁) = ⊥-elim (WF.U≢ℕ! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B PE.refl (ne-ins x x₁ x₂ x₃) (ne x₄) = ⊥-elim (WF.U≢ne! x₂ (sym A≡B))
    transConv↓Term  Γ≡Δ A≡B PE.refl (ne-ins t u x x₁) (ℕ-ins x₂) =
      ⊥-elim (WF.ℕ≢ne! x (sym A≡B))
    transConv↓Term Γ≡Δ A≡B PE.refl (ne-ins x x₁ x₂ x₃) (η-eq x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) = ⊥-elim (WF.Π≢ne x₂ (sym A≡B))
    transConv↓Term Γ≡Δ A≡B PE.refl (zero-refl x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =  ⊥-elim (WF.ℕ≢Π! A≡B)
    transConv↓Term Γ≡Δ A≡B PE.refl (suc-cong x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =  ⊥-elim (WF.ℕ≢Π! A≡B)
    transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne x₈) = ⊥-elim (WF.U≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-refl x₈) = ⊥-elim (WF.U≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Empty-refl x₈) = ⊥-elim (WF.U≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Π-cong x₀ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) = ⊥-elim (WF.U≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Id-cong x₁₃ x₁₄ x₁₅) = ⊥-elim (WF.U≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-ins x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne-ins x₈ x₉ x₁₀ x₁₁) = ⊥-elim (WF.Π≢ne x₁₀ A≡B)
    transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (zero-refl x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (suc-cong x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
  
    transConv↓Term Γ≡Δ A≡B el (ne x) (U-refl x₁ x₂) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ne x) (U-refl x₁ x₂) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne x) (ℕ-refl x₁) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ne x) (ℕ-refl x₁) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne x) (Ind-refl x₁) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ne x) (Ind-refl x₁) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne x) (Empty-refl x₁) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ne x) (Empty-refl x₁) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne x) (Id-cong x₁ x₂ x₃) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ne x) (Id-cong x₁ x₂ x₃) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne x) (zero-refl x₁) = ⊥-elim (WF.U≢ℕ! A≡B)
    transConv↓Term Γ≡Δ A≡B el (ne x) (suc-cong x₁) = ⊥-elim (WF.U≢ℕ! A≡B)
    transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
    transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
    transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne x₉) with ne~↓! x₉
    transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne x₉) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ℕ-ins x₉) = ⊥-elim (WF.U≢ℕ! A≡B)
    transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne-ins x₉ x₁₀ x₁₁ x₁₂) with ne~↓! x₁₂
    transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne-ins x₉ x₁₀ x₁₁ x₁₂) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (Id-cong x x₁ x₂) (ne x₃) with ne~↓! x₃
    transConv↓Term Γ≡Δ A≡B el (Id-cong x x₁ x₂) (ne x₃) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (Id-cong x x₁ x₂) (ne-ins x₃ x₄ x₅ x₆) with ne~↓! x₆
    transConv↓Term Γ≡Δ A≡B el (Id-cong x x₁ x₂) (ne-ins x₃ x₄ x₅ x₆) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (WF.U≢ℕ! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (zero-refl x₁) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (zero-refl x₁) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (suc-cong x₁) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (suc-cong x₁) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (ℕ-refl x₄) with ne~↓! x₃
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (ℕ-refl x₄) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Empty-refl x₄) with ne~↓! x₃
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Empty-refl x₄) | _ , _ , () 
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) with ne~↓! x₃
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) | _ , _ , () 
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) with ne~↓! x₃
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) | _ , _ , () 
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (zero-refl x₄) with ne~↓! x₃ 
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (zero-refl x₄) | _ , _ , () 
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (suc-cong x₄) with ne~↓! x₃
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (suc-cong x₄) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ℕ-ins x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ℕ-ins x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ℕ-ins x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ℕ-ins x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (U-refl x x₁) (ne x₂) with ne~↓! x₂
    transConv↓Term Γ≡Δ A≡B el (U-refl x x₁) (ne x₂) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (ne x) (Ind-ins x₁) = ⊥-elim (WF.U≢Ind! A≡B)
    transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (Ind-ins x₉) = ⊥-elim (WF.U≢Ind! A≡B)
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (ne x₁) = ⊥-elim (WF.U≢Ind! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (WF.U≢Ind! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (ℕ-ins x₁) = ⊥-elim (WF.Ind≢ℕ! A≡B)
    transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (Ind-ins x₁) = ⊥-elim (WF.ℕ≢Ind! A≡B)
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (ne-ins x₁ x₂ x₃ x₄) = ⊥-elim (WF.Ind≢ne! x₃ A≡B)
    transConv↓Term Γ≡Δ A≡B PE.refl (ne-ins t u x x₁) (Ind-ins x₂) =
      ⊥-elim (WF.Ind≢ne! x (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (zero-refl x₁) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (zero-refl x₁) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (suc-cong x₁) with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (suc-cong x₁) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (Ind-ins x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (zero-refl x) (Ind-ins x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (Ind-ins x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (suc-cong x) (Ind-ins x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B PE.refl (Ind-ins x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.Ind≢Π! A≡B)
    transConv↓Term {Γ = Γ} Γ≡Δ A≡B el (η-eq {F = F} {rF = rF} {lF = lF} {lG = lG} {l = l} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Ind-ins x₈) = ⊥-elim (WF.Π≢Ind! A≡B)

    transConv↓Term Γ≡Δ A≡B el (Ind-refl x) (Ind-refl x₁) _ = Ind-refl x , leS le0

    transConv↓Term Γ≡Δ A≡B PE.refl (Ind-refl x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.U≢Π! A≡B)
    transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Ind-refl x₈) = ⊥-elim (WF.U≢Π! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (Ind-refl x) (ne x₁) with ne~↓! x₁
    transConv↓Term Γ≡Δ A≡B el (Ind-refl x) (ne x₁) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (Ind-refl x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
    transConv↓Term Γ≡Δ A≡B el (Ind-refl x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Ind-refl x₄) with ne~↓! x₃
    transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Ind-refl x₄) | _ , _ , ()
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (Ind-refl x₄) = ⊥-elim (WF.U≢Ind! (sym A≡B))
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (ctr-cong _ _ _ _ _) _ with ne~↓! x
    transConv↓Term Γ≡Δ A≡B el (Ind-ins x) (ctr-cong _ _ _ _ _) _ | _ , _ , ()

    transConv↓Term {n = 1+ n} {v = v} {Γ = Γ} {Δ = Δ} {l' = l'} Γ≡Δ A≡B el
                   (ctr-cong {ind = ind} {j = j} {args = args} {args' = args'} ⊢Γ ind∈ argsTypeEq len ps) e' (leS fuel) =
      let wB , _ , _ = whnfConv↓Term e'
          B≡Ind = Ind≡A A≡B wB
          e'B = PE.subst (λ B' → Δ ⊢ ctr i j args' [conv↓] v ∷ B' ^ l') B≡Ind e'
          e'Ind = PE.subst (λ l'' → Δ ⊢ ctr i j args' [conv↓] v ∷ Ind i ^ l'') (PE.sym el) e'B
          sizeEq = PE.trans (sizeSubst-gen (λ l'' → Δ ⊢ ctr i j args' [conv↓] v ∷ Ind i ^ l'') sizeConv↓Term e'B (PE.sym el))
                             (sizeSubst-gen (λ B' → Δ ⊢ ctr i j args' [conv↓] v ∷ B' ^ l') sizeConv↓Term e' B≡Ind)
          fuelInd = PE.subst (λ s → (sizeConv↓Term (ctr-cong ⊢Γ ind∈ argsTypeEq len ps) + s) <= n) (PE.sym sizeEq) fuel
          e'' , sz = go e'Ind PE.refl fuelInd
      in e'' , PE.subst (λ s → sizeConv↓Term e'' <= (sizeConv↓Term (ctr-cong ⊢Γ ind∈ argsTypeEq len ps) + s)) sizeEq sz
      where
      i : Nat
      i = SI.SInd.name ind
      go : ∀ {i' t u} (e2 : Δ ⊢ t [conv↓] u ∷ Ind i' ^ ι ⁰)
         → t PE.≡ ctr i j args'
         → (sizeConv↓Term (ctr-cong ⊢Γ ind∈ argsTypeEq len ps) + sizeConv↓Term e2) <= n
         → ∃ λ (e'' : Γ ⊢ ctr i j args [conv↓] u ∷ Ind i ^ ι ⁰)
             → (sizeConv↓Term e'' <= (sizeConv↓Term (ctr-cong ⊢Γ ind∈ argsTypeEq len ps) + sizeConv↓Term e2))
      go (ne-ins _ _ _ x) eq _ = ⊥-elim (Ctr≢ne (proj₁ (proj₂ (ne~↓! x))) (PE.sym eq))
      go (Ind-ins x) eq _ = ⊥-elim (Ctr≢ne (proj₁ (proj₂ (ne~↓! x))) (PE.sym eq))
      go (ctr-cong {args = args2} {args' = args2'} ⊢Γ' ind∈' argsTypeEq' len' qs) eq fuel2
        with ctr-PE-injectivity eq
      ... | name≡ , PE.refl , PE.refl with SI.name-inj senv (proj₁ swf) ind∈' ind∈ name≡
      ... | PE.refl =
        let rs , sizeRs = transAll ps qs (le-refl _) (le-refl _)
        in  ctr-cong ⊢Γ ind∈ argsTypeEq len rs , <=-trans (leS sizeRs) (<=-help-rigid1 {a = sizeConv↑TermAll ps} {b = sizeConv↑TermAll qs})
        where
        transAll : ∀ {as as' as''}
                 → (ps' : All₂ (λ a a' → Γ ⊢ a [conv↑] a' ∷ Ind i ^ ι ⁰) as as')
                 → (qs' : All₂ (λ a a' → Δ ⊢ a [conv↑] a' ∷ Ind i ^ ι ⁰) as' as'')
                 → sizeConv↑TermAll ps' <= sizeConv↑TermAll ps
                 → sizeConv↑TermAll qs' <= sizeConv↑TermAll qs
                 → ∃ λ (rs : All₂ (λ a a' → Γ ⊢ a [conv↑] a' ∷ Ind i ^ ι ⁰) as as'')
                     → (sizeConv↑TermAll rs <= (sizeConv↑TermAll ps' + sizeConv↑TermAll qs'))
        transAll []ₐ []ₐ _ _ = []ₐ , le0
        transAll (p ∷ₐ ps') (q ∷ₐ qs') boundA boundB =
          let p<=SA = <=-trans (le-plus-right (sizeConv↑TermAll ps')) boundA
              q<=SB = <=-trans (le-plus-right (sizeConv↑TermAll qs')) boundB
              pqFuel = <=-trans (leS (<=-cong-+ p<=SA q<=SB))
                                 (<=-trans (<=-help-rigid1 {a = sizeConv↑TermAll ps} {b = sizeConv↑TermAll qs}) fuel2)
              r , sizeR = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (univ (Indⱼ ⊢Γ))) p q pqFuel
              boundA' = <=-trans (le-plus-left (sizeConv↑Term p) (le-refl _)) boundA
              boundB' = <=-trans (le-plus-left (sizeConv↑Term q) (le-refl _)) boundB
              rs' , sizeRs' = transAll ps' qs' boundA' boundB'
          in r ∷ₐ rs' ,
             <=-trans (<=-cong-+ sizeR sizeRs')
                      (≡-to-<= (comm-lemma₁ (sizeConv↑Term p) (sizeConv↑Term q) (sizeConv↑TermAll ps') (sizeConv↑TermAll qs')))

    transConv↓Term {A = gen (Ukind _ _) Tools.List.[]} {B = gen (Indkind _) Tools.List.[]} Γ≡Δ A≡B el e e' _ =
      ⊥-elim (WF.U≢Ind! A≡B)
    transConv↓Term {_} {_} {_} {_} {gen Natkind Tools.List.[]} {gen (Indkind _) Tools.List.[]} {_} {_} {ι ⁰} {ι ⁰} Γ≡Δ A≡B el e e' _ =
      ⊥-elim (WF.ℕ≢Ind! A≡B)
    transConv↓Term {B = gen (Indkind _) Tools.List.[]} Γ≡Δ A≡B PE.refl (η-eq _ _ _ _ _ _ _ _) e' _ =
      ⊥-elim (WF.Π≢Ind! A≡B)
    transConv↓Term {_} {_} {_} {_} {_} {gen (Indkind _) Tools.List.[]} {_} {_} {ι ⁰} {ι ⁰} Γ≡Δ A≡B el (ne-ins _ _ n _) e' _ =
      ⊥-elim (WF.Ind≢ne! n (sym A≡B))

    -- transConv↓Term = {!!}
  
  -- Transitivity of algorithmic equality of types of the same context.
  transConv : ∀ {A B C r Γ}
            → Γ ⊢ A [conv↑] B ^ r
            → Γ ⊢ B [conv↑] C ^ r
            → Γ ⊢ A [conv↑] C ^ r
  transConv A<>B B<>C =
    let Γ≡Γ = reflConEq (wfEq (soundnessConv↑ A<>B))
    in  proj₁ (transConv↑ Γ≡Γ A<>B B<>C (le-refl _))
  
  -- Transitivity of algorithmic equality of terms of the same context.
  transConvTerm : ∀ {t u v A Γ l}
                → Γ ⊢ t [conv↑] u ∷ A ^ l
                → Γ ⊢ u [conv↑] v ∷ A ^ l
                → Γ ⊢ t [conv↑] v ∷ A ^ l
  transConvTerm t<>u u<>v =
    let t≡u = soundnessConv↑Term t<>u
        Γ≡Γ = reflConEq (wfEqTerm t≡u)
        ⊢A , _ , _ = syntacticEqTerm t≡u
    in proj₁ (transConv↑Term PE.refl Γ≡Γ (refl ⊢A) t<>u u<>v (le-refl _))
  
  trans~↑!Term : ∀ {t u v A Γ l}
                → Γ ⊢ t ~ u ↑% A ^ l
                → Γ ⊢ u ~ v ↑% A ^ l
                → Γ ⊢ t ~ v ↑% A ^ l
  trans~↑!Term t<>u u<>v =
    let _ , _ , t≡u = soundness~↑% t<>u
        Γ≡Γ = reflConEq (wfEqTerm t≡u)
    in  trans~↑% Γ≡Γ t<>u u<>v
    
  trans~↓!-simpl : ∀ {t u v A B Γ l}
                → Γ ⊢ t ~ u ↓! A ^ l
                → Γ ⊢ u ~ v ↓! B ^ l
                → ∃ λ C → Whnf C ×  Γ ⊢ t ~ v ↓! C ^ l × Γ ⊢ A ≡ C ^ [ ! , l ]
  trans~↓!-simpl t<>u u<>v =
    let t≡u = soundness~↓! t<>u
        Γ≡Γ = reflConEq (wfEqTerm t≡u)
        ⊢A , _ , _ = syntacticEqTerm t≡u
        a , b , c , d , _  = trans~↓! PE.refl Γ≡Γ t<>u u<>v (le-refl _)
    in a , b , c , d
  
  trans~↑!-simpl : ∀ {t u v A B Γ l}
                → Γ ⊢ t ~ u ↑! A ^ l
                → Γ ⊢ u ~ v ↑! B ^ l
                → ∃ λ C → Γ ⊢ t ~ v ↑! C ^ l × Γ ⊢ A ≡ C ^ [ ! , l ]
  trans~↑!-simpl t<>u u<>v =
    let t≡u = soundness~↑! t<>u
        Γ≡Γ = reflConEq (wfEqTerm t≡u)
        ⊢A , _ , _ = syntacticEqTerm t≡u
        a , b , c , _  = trans~↑! PE.refl Γ≡Γ t<>u u<>v (le-refl _)
    in a , b , c
  