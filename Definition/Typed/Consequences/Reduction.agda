import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Consequences.Reduction (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Definition.Typed.Properties senv equivs
open import Definition.Typed.EqRelInstance senv equivs
open import Definition.LogicalRelation senv equivs
open import Definition.LogicalRelation.Properties senv equivs
open import Definition.LogicalRelation.Fundamental.Reducibility senv swf equivs
import Tools.PropositionalEquality as PE
open import Tools.Product
-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A rA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ^ rA)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm′ (Uᵣ′ _ _ r l _ e d) = Univ r l , Uₙ , PE.subst (λ ll → _ ⊢ _ :⇒*: Univ r l ^ [ ! , ll ]) e d
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Indᵣ {i = i} D) = Ind i , Indₙ , D
whNorm′ (Emptyᵣ D) = sEmpty , Emptyₙ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Πᵣ {l = l} (Πᵣ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) = Π F ^ rF ° lF ▹ G ° lG ° l ^ ! , Πₙ , D
whNorm′ (Idᵣ′ A t u _ D ⊢F ⊢G _ A≡A) = Id A t u , Idₙ , D
whNorm′ (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) = Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % , Πₙ , D
whNorm′ (emb emb< [A]) = whNorm′ [A]
whNorm′ (emb ∞< [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A rA Γ} → Γ ⊢ A ^ rA → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm A = whNorm′ (reducible A)

-- whNorm-conv : ∀ {A rA Γ} → Γ ⊢ A ≡ B ^ rA → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
-- whNorm-conv A = whNorm′ (reducible A)

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A Γ l lA} ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , lA ]) → Γ ⊩⟨ l ⟩ a ∷ A ^ [ ! , lA ] / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ lA
whNormTerm′ (Uᵣ′ _ _ r l _ e dU) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA ,
  conv:⇒*: (PE.subst (λ ll → _ ⊢ _ :⇒*: _ ∷ _ ^ ll) e d)
    (sym (subset* (red (PE.subst (λ ll → _ ⊢ _ :⇒*: Univ r l ^ [ ! , ll ]) e dU))))
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Indᵣ x) (Indₜ k d k≡k prop) =
  let indN = inductive′ prop
  in  k , inductiveWhnf indN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ rF lF lG lF≤ lG≤  F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb emb< [A]) [a] = whNormTerm′ [A] [a]
whNormTerm′ (emb ∞< [A]) [a] = whNormTerm′ [A] [a]

-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A Γ lA} → Γ ⊢ a ∷ A ^ [ ! , lA ] → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ lA
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]
