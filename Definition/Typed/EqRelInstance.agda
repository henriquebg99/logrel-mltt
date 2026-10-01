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
open import Tools.List using (All₃; []ₐ; _∷ₐ_)

-- Pointwise equality of lists of terms, as a judgement.
All₃-⊢All : ∀ {Γ ms ms' As r}
          → All₃ (λ m m' A → Γ ⊢ m ≡ m' ∷ A ^ r) ms ms' As
          → Γ ⊢All ms ≡ ms' ∷ As ^ r
All₃-⊢All []ₐ = εⱼ
All₃-⊢All (p ∷ₐ ps) = consⱼ p (All₃-⊢All ps)

Urefl   : ∀ {r l Γ} → ⊢ Γ → Γ ⊢ (Univ r l) ≡ (Univ r l) ^ [ ! , next l ]
Urefl {l = ⁰} ⊢Γ = refl (univ (univ 0<1 ⊢Γ))
Urefl {l = ¹} ⊢Γ = refl (Uⱼ ⊢Γ)

instance eqRelInstance : EqRelSet   
eqRelInstance = eqRel _⊢_≡_^_ _⊢_≡_∷_^_ _⊢_≡_∷_^_
                      idᶠ idᶠ idᶠ univ un-univ≡
                      sym genSym genSym trans genTrans genTrans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      Urefl (refl ∘ᶠ univ 0<1) (λ ⊢Γ i∈ → refl (Indⱼ′ ⊢Γ i∈)) (refl ∘ᶠ Emptyⱼ)
                      Π-cong
                      ctr-cong
                      (λ lF lG x x₁ x₂ x₃ x₄ x₅ → η-eq lF lG x x₁ x₂ x₅)
                      genVar app-cong (λ ind∈ P≡P′ t≡t′ ms≡ms′ → IndRect-cong ind∈ P≡P′ t≡t′ (All₃-⊢All ms≡ms′)) Emptyrec-cong
                      Id-cong
                      cast-cong
                      (λ {i} i∈ A≡A t≡t e e' → cast-cong A≡A (refl (Indⱼ′ (wfTerm e) i∈)) t≡t e e')
                      cast-cong
                      (λ A t~u ⊢t ⊢e → trans (cast-refl A ⊢e ⊢t) (conv t~u (univ A)))
                      (λ {i} ⊢Γ i∈ → cast-cong (refl (Indⱼ′ ⊢Γ i∈)))
                      cast-cong
                      (λ {i} i∈ ⊢A ⊢P P → cast-cong (refl (Indⱼ′ (wf (univ ⊢A)) i∈)) P)
                      (λ {i} i∈ ⊢A ⊢P P → cast-cong P (refl (Indⱼ′ (wf (univ ⊢A)) i∈)))
                      (λ {i} {j} i∈ j∈ i≢j t≡t' e e' → cast-cong (refl (Indⱼ′ (wfTerm e) i∈)) (refl (Indⱼ′ (wfTerm e) j∈)) t≡t' e e')
                      (λ ⊢A ⊢P P ⊢A' ⊢P' P' → cast-cong P P')
                      (λ ⊢A ⊢P P ⊢A' ⊢P' P' → cast-cong P P')
                      proof-irrelevance
