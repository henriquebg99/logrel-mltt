import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.EqRelInstance (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv swf equivs
open import Definition.Typed.Weakening senv equivs
open import Definition.Typed.Reduction senv swf equivs
open import Definition.Typed.EqualityRelation senv equivs
open import Tools.Function
Urefl   : ∀ {r l Γ} → ⊢ Γ → Γ ⊢ (Univ r l) ≡ (Univ r l) ^ [ ! , next l ]
Urefl {l = ⁰} ⊢Γ = refl (univ (univ 0<1 ⊢Γ))
Urefl {l = ¹} ⊢Γ = refl (Uⱼ ⊢Γ)

instance eqRelInstance : EqRelSet   
eqRelInstance = eqRel _⊢_≡_^_ _⊢_≡_∷_^_ _⊢_≡_∷_^_
                      idᶠ idᶠ idᶠ univ un-univ≡
                      sym genSym genSym trans genTrans genTrans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      Urefl (refl ∘ᶠ univ 0<1) (refl ∘ᶠ ℕⱼ) (λ ⊢Γ i∈ → refl (Indⱼ′ ⊢Γ i∈)) (refl ∘ᶠ Emptyⱼ)
                      Π-cong (refl ∘ᶠ zeroⱼ) suc-cong
                      ctr-cong
                      (λ lF lG x x₁ x₂ x₃ x₄ x₅ → η-eq lF lG x x₁ x₂ x₅)
                      genVar app-cong natrec-cong IndRect-cong Emptyrec-cong
                      Id-cong
                      cast-cong (λ A≡A t≡t e e' → cast-cong A≡A (refl (ℕⱼ (wfTerm e))) t≡t e e')
                      (λ {i} i∈ A≡A t≡t e e' → cast-cong A≡A (refl (Indⱼ′ (wfTerm e) i∈)) t≡t e e')
                      cast-cong
                      (λ A t~u ⊢t ⊢e → trans (cast-refl A ⊢e ⊢t) (conv t~u (univ A)))
                      (λ t~u ⊢t ⊢e → trans (cast-refl (refl (ℕⱼ (wfTerm ⊢t))) ⊢e ⊢t) t~u)
                      (λ ⊢Γ → cast-cong (refl (ℕⱼ ⊢Γ)))
                      (λ {i} ⊢Γ i∈ → cast-cong (refl (Indⱼ′ ⊢Γ i∈)))
                      cast-cong
                      (λ ⊢A ⊢P P → cast-cong (refl (ℕⱼ (wf (univ ⊢A)))) P)
                      (λ {i} i∈ ⊢A ⊢P P → cast-cong (refl (Indⱼ′ (wf (univ ⊢A)) i∈)) P)
                      (λ ⊢A ⊢P P → cast-cong P (refl (ℕⱼ (wf (univ ⊢A)))))
                      (λ {i} i∈ ⊢A ⊢P P → cast-cong P (refl (Indⱼ′ (wf (univ ⊢A)) i∈)))
                      (λ {i} i∈ t≡t' e e' → cast-cong (refl (Indⱼ′ (wfTerm e) i∈)) (refl (ℕⱼ (wfTerm e))) t≡t' e e')
                      (λ {i} i∈ t≡t' e e' → cast-cong (refl (ℕⱼ (wfTerm e))) (refl (Indⱼ′ (wfTerm e) i∈)) t≡t' e e')
                      (λ {i} {j} i∈ j∈ i≢j t≡t' e e' → cast-cong (refl (Indⱼ′ (wfTerm e) i∈)) (refl (Indⱼ′ (wfTerm e) j∈)) t≡t' e e')
                      (λ ⊢A ⊢P P ⊢A' ⊢P' P' → cast-cong P P')
                      (λ ⊢A ⊢P P ⊢A' ⊢P' P' → cast-cong P P')
                      proof-irrelevance
