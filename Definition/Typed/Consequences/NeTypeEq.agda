import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.NeTypeEq (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Typed.EqRelInstance senv swf equivs
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.Weakening senv equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Tools.Product
import Tools.List as TL
import Tools.PropositionalEquality as PE
-- to be moved in Untyped
typelevel-injectivity : ∀ {r r' l l'} → [ r , l ] PE.≡ [ r' , l' ] → r PE.≡ r' × l PE.≡ l'
typelevel-injectivity PE.refl = PE.refl , PE.refl

-- Helper function for the same variable instance of a context have equal types.
varTypeEq′ : ∀ {n R rR T rT Γ} → n ∷ R ^ rR ∈ Γ → n ∷ T ^ rT ∈ Γ → R PE.≡ T × rR PE.≡ rT
varTypeEq′ here here = PE.refl , PE.refl
varTypeEq′ (there n∷R) (there n∷T) with varTypeEq′ n∷R n∷T
... | PE.refl , PE.refl = PE.refl , PE.refl

-- The same variable instance of a context have equal types.
varTypeEq : ∀ {x A B rA rB Γ} → Γ ⊢ A ^ rA → Γ ⊢ B ^ rB
          → x ∷ A ^ rA ∈ Γ
          → x ∷ B ^ rB ∈ Γ
          → Γ ⊢ A ≡ B ^ rA × rA PE.≡ rB
varTypeEq A B x∷A x∷B with varTypeEq′ x∷A x∷B
... | PE.refl , PE.refl = refl A , PE.refl

-- The same neutral term have equal types.
-- to use this with different relevances rA rB we need unicity of relevance for types

-- ctr and IndRect are gen-spines built with map, so dual Ctrⱼ / IndRectⱼ matching
-- does not unify. We therefore state their inversions over an arbitrary spine xs.
ctrTypeEq′ : ∀ {i j xs T r l Γ} → Γ ⊢ gen (Ctrkind i j) xs ∷ T ^ [ r , l ] →
  r PE.≡ ! × l PE.≡ ι ⁰ × Γ ⊢ T ≡ Ind i ^ [ ! , ι ⁰ ]
ctrTypeEq′ (Ctrⱼ ⊢Γ ind∈ _ _) = PE.refl , PE.refl , refl (univ (Indⱼ ⊢Γ ind∈))
ctrTypeEq′ (conv X x) = let er , el , eq = ctrTypeEq′ X in er , el ,
  trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) el (PE.subst (λ r → _ ⊢ _ ≡ _ ^ [ r , _ ]) er x))) eq

IndRectTypeEq′ : ∀ {i lG P t xs T r l Γ} → Γ ⊢ gen (IndRectkind i lG) (⟦ 1 , P ⟧ TL.∷ ⟦ 0 , t ⟧ TL.∷ xs) ∷ T ^ [ r , l ] →
  Γ ∙ Ind i ^ [ ! , ι ⁰ ] ⊢ P ^ [ r , ι lG ] × l PE.≡ ι lG × Γ ⊢ T ≡ P [ t ] ^ [ r , ι lG ]
IndRectTypeEq′ (IndRectⱼ _ _ ⊢P ⊢t _) = ⊢P , PE.refl , refl (substType ⊢P ⊢t)
IndRectTypeEq′ (conv X x) = let ⊢P , el , eq = IndRectTypeEq′ X in ⊢P , el ,
  trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) el x)) eq

neTypeEq : ∀ {t A B lA lA' Γ} → Neutral t → Γ ⊢ t ∷ A ^ [ ! , lA ] → Γ ⊢ t ∷ B ^ [ ! , lA' ] →
  lA PE.≡ lA' × Γ ⊢ A ≡ B ^ [ ! , lA ]
neTypeEq (var x) (var x₁ x₂) (var x₃ x₄) =
  let V , e = varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
      _ , el = typelevel-injectivity e
  in el , V 
neTypeEq (∘ₙ neT) (_ ▹ _ ▹ _ ▹ t∷A ∘ⱼ t∷A₁) (_ ▹ _ ▹ _ ▹ t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | e , q = let _ , _ , _ , elG , w = injectivity q
              in PE.cong _ elG , substTypeEq w (genRefl t∷A₁)
neTypeEq (natrecₙ neT) (natrecⱼ _ x t∷A t∷A₁ t∷A₂) (natrecⱼ _ x₁ t∷B t∷B₁ t∷B₂) =
  PE.refl , refl (substType x₁ t∷B₂)
neTypeEq Emptyrecₙ (Emptyrecⱼ x t∷A) (Emptyrecⱼ x₁ t∷B) =
  PE.refl , refl x₁
neTypeEq (IndRectₙ neT) t∷A t∷B =
  let _ , elA , eqA = IndRectTypeEq′ t∷A
      _ , elB , eqB = IndRectTypeEq′ t∷B
  in PE.trans elA (PE.sym elB) , PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ ! , l ]) (PE.sym elA) (trans eqA (sym eqB))
neTypeEq X (castⱼ Y Y₁ Y₂ Y₃)  (castⱼ Z Z₁ Z₂ Z₃) = PE.refl , refl (univ Y₁) 
neTypeEq x (conv t∷A x₁) t∷B = 
  let e , q = neTypeEq x t∷A t∷B
  in e , trans (sym x₁) q 
neTypeEq x t∷A (conv t∷B x₃) =
  let e , q = neTypeEq x t∷A t∷B
  in e , trans q (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ]) (PE.sym e) x₃) 

natTypeEq : ∀ {A rA lA Γ} → Γ ⊢ ℕ ∷ A ^ [ rA , lA ] → rA PE.≡ ! × lA PE.≡ ι ¹ × Γ ⊢ A ≡ U ⁰ ^ [ ! , ι ¹ ]
natTypeEq (ℕⱼ x) = PE.refl , PE.refl , refl (univ (univ 0<1 x))
natTypeEq (conv X x) = let eqrA , eqlA , eqAU = natTypeEq X in eqrA , eqlA ,
  trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) eqlA (PE.subst (λ r → _ ⊢ _ ≡ _ ^ [ r , _ ]) eqrA x))) eqAU 

emptyTypeEq : ∀ {A rA lA Γ} → Γ ⊢ sEmpty ∷ A ^ [ rA , lA ] →
  rA PE.≡ ! × lA PE.≡ next ⁰ × Γ ⊢ A ≡ SProp ^ [ ! , next ⁰ ]
emptyTypeEq (Emptyⱼ x) = PE.refl , PE.refl , refl (Ugenⱼ x) 
emptyTypeEq (conv X x) = let eqrA , eqlA , eqAU = emptyTypeEq X in eqrA , eqlA , 
 trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) eqlA (PE.subst (λ r → _ ⊢ _ ≡ _ ^ [ r , _ ]) eqrA x))) eqAU 
