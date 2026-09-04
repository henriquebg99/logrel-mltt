open import Definition.Typed.EqualityRelation
import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.Cast {{eqrel : EqRelSet}} where
open EqRelSet {{...}}
open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Twk
open import Definition.Typed.EqualityRelation
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Weakening as Lwk
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
-- open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.ShapeView
-- open import Definition.LogicalRelation.Substitution.Introductions.Pi
-- open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Castlemmas
open import Definition.LogicalRelation.Substitution.Introductions.Ind using (≅AllInd)
open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.List using (All; All₂; []ₐ; _∷ₐ_; map; length; length-map)
open import Tools.Nat
import Tools.Nullary as Nullary
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU

import Definition.LogicalRelation.EquivRed as ERd
postulate equivRed : ERd.EquivRed

~-irrelevanceTerm : ∀ {t t' u u' A A' r Γ} (eqA : A PE.≡ A') (eqt : t PE.≡ t') (equ : u PE.≡ u')
                  → Γ ⊢ t ~ u ∷ A ^ r
                  → Γ ⊢ t' ~ u' ∷ A' ^ r
~-irrelevanceTerm PE.refl PE.refl PE.refl X = X

inversion-Ctr : ∀ {Γ i j args C r}
  → Γ ⊢ ctr i j args ∷ C ^ r
  → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
inversion-Ctr {Γ} {i} {j} {args} ⊢t = go ⊢t PE.refl
  where
    go : ∀ {t A r} → Γ ⊢ t ∷ A ^ r → t PE.≡ ctr i j args
       → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ]
    go (Ctrⱼ {i = i′} {j′} {args = args′} _ ⊢args) e =
      let i≡ , j≡ , args≡ = ctr-PE-injectivity e
      in  PE.subst₃ (λ i j args → Γ ⊢All args ∷ map emb-stype (SU.ctrArgsTypeList i j) ^ [ ! , ι ⁰ ])
                    i≡ j≡ args≡ ⊢args
    go (conv x _) e = go x e
    go (univ _ _) ()
    go (ℕⱼ _) ()
    go (ℕ2ⱼ _) ()
    go (Emptyⱼ _) ()
    go (Πⱼ _ ▹ _ ▹ _ ▹ _) ()
    go (var _ _) ()
    go (lamⱼ _ _ _ _) ()
    go (_▹_▹_▹_∘ⱼ_ _ _ _ _ _) ()
    go (fstⱼ _ _ _ _ _) ()
    go (sndⱼ _ _ _ _ _) ()
    go (zeroⱼ _) ()
    go (sucⱼ _) ()
    go (zero2ⱼ _) ()
    go (suc2ⱼ _) ()
    go (natrecⱼ _ _ _ _ _) ()
    go (natrec2ⱼ _ _ _ _ _) ()
    go (Indⱼ _) ()
    go (IndRectⱼ _ _ _ _) ()
    go (Emptyrecⱼ _ _) ()
    go (Idⱼ _ _ _) ()
    go (Idreflⱼ _) ()
    go (transpⱼ _ _ _ _ _ _) ()
    go (castⱼ _ _ _ _) ()
    go (equiv-eqⱼ _) ()

[cast]irr : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ % , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ % , ι ⁰ ]) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ % , ι ⁰ ] / [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ % ⁰) A B ^ [ % , ι ⁰ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ % , ι ⁰ ] / [B]
[cast]irr {A} {B} ⊢Γ [A] [B] {t} {e} [t] ⊢e =
  let ⊢A = escape {l = ι ⁰} {A = A} [A]
      ⊢B = escape {l = ι ⁰} {A = B} [B]
      ⊢t = escapeTerm {l = ι ⁰} {A = A} [A] [t]
  in logRelIrr [B] (castⱼ (un-univ ⊢A) (un-univ ⊢B) ⊢e ⊢t)

[castext]irr : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ % , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ % , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ % , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ % , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ % , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ % , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ % , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ % , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ % , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ % ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ % ⁰) A′ B′ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ % , ι ⁰ ] / [B])
[castext]irr {A} {A′} {B} {B′} ⊢Γ [A] [A′] [A≡A′] [B] [B′] [B≡B′] [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let ⊢A = escape {l = ι ⁰} {A = A} [A]
      ⊢B = escape {l = ι ⁰} {A = B} [B]
      ⊢A′ = escape {l = ι ⁰} {A = A′} [A′]
      ⊢B′ = escape {l = ι ⁰} {A = B′} [B′]
      ⊢t = escapeTerm {l = ι ⁰} {A = A} [A] [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} [A′] [t′]
  in logRelIrrEq [B] (castⱼ (un-univ ⊢A) (un-univ ⊢B) ⊢e ⊢t) (conv (castⱼ (un-univ ⊢A′) (un-univ ⊢B′) ⊢e′ ⊢t′) (sym (≅-eq (escapeEq [B] [B≡B′]))))


[cast]Ne : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] :  Γ ⊩ne A ^[ ! , ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ]) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ne [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ ! ⁰) A B ^ [ % , ι ⁰ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / [B]
[cast]Ne {A} {B} ⊢Γ (ne K D neK K≡K) (ℕᵣ D') {t} {e} [t] ⊢e =
  let [[ ⊢A , ⊢K , DK ]] = D
      ⊢A≡K = subset* DK
      [[ ⊢B , ⊢N , DN ]] = D'
      ⊢B≡N = subset* DN
      ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡N)))
      ⊢e'' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      cast~cast = ~-conv (~-castneℕ K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ne′ K D neK K≡K) (reflEqTerm {l = ι ⁰} (ne′ K D neK K≡K) [t])) ⊢A≡K) ⊢e' ⊢e') (sym ⊢B≡N)
      ⊢t = escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]
  in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} (ℕᵣ D') (castnℕₙ neK)
                 (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢e'' (conv ⊢t ⊢A≡K) (un-univ:⇒*: D')))
                 cast~cast

[cast]Ne {A} {B} ⊢Γ (ne K D neK K≡K) (ℕ2ᵣ D') {t} {e} [t] ⊢e =
  let [[ ⊢A , ⊢K , DK ]] = D
      ⊢A≡K = subset* DK
      [[ ⊢B , ⊢N , DN ]] = D'
      ⊢B≡N = subset* DN
      ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡N)))
      ⊢e'' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      cast~cast = ~-conv (~-castneℕ2 K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ne′ K D neK K≡K) (reflEqTerm {l = ι ⁰} (ne′ K D neK K≡K) [t])) ⊢A≡K) ⊢e' ⊢e') (sym ⊢B≡N)
      ⊢t = escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]
  in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} (ℕ2ᵣ D') (castnℕ2ₙ neK)
                 (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢e'' (conv ⊢t ⊢A≡K) (un-univ:⇒*: D')))
                 cast~cast

[cast]Ne {A} {B} ⊢Γ (ne K D neK K≡K) (ne′ K' D' neK' K≡K') {t} {e} (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) ⊢e =
  let [[ ⊢A , ⊢K , DK ]] = D
      ⊢A≡K = subset* DK
      [[ ⊢B , ⊢K' , DK' ]] = D'
      ⊢B≡K' = subset* DK'
      ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡K')))
      ⊢e'' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      [t] = neₜ k d (neNfₜ neK₁ ⊢k k≡k)
      cast~cast = ~-cast K≡K K≡K' k≡k ⊢e' ⊢e'
      ⊢t = escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]
  in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} (ne′ K' D' neK' K≡K') (castₙ neK neK' neK₁)
                 (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D))
                 (transTerm:⇒:* (CastRedR*Term ⊢K neK ⊢e'' (conv ⊢t ⊢A≡K) (un-univ:⇒*: D'))
                                (conv:⇒*: (CastRedTerm*Term ⊢K neK ⊢K' neK' ⊢e' d) (sym ⊢B≡K'))))
                 (~-conv cast~cast (sym ⊢B≡K'))

[cast]Ne {A} {B} ⊢Γ (ne K D neK K≡K) (Πᵣ′ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D' ⊢F ⊢G A≡A [F] [G] G-ext) {t} {e} [t] ⊢e =
  let [[ ⊢A , ⊢K , DK ]] = D
      ⊢A≡K = subset* DK
      [[ ⊢B , ⊢N , DN ]] = D'
      ⊢B≡N = subset* DN
      ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡N)))
      ⊢e'' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      cast~cast = ~-conv (~-castneΠ K≡K (≅-un-univ A≡A) (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ne′ K D neK K≡K) (reflEqTerm {l = ι ⁰} (ne′ K D neK K≡K) [t])) ⊢A≡K) ⊢e' ⊢e') (sym ⊢B≡N)
      ⊢t = escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]
  in neuTerm:⇒*: {t = cast ⁰ A B e t} (Πᵣ′ rF _ _ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D' ⊢F ⊢G A≡A [F] [G] G-ext) (castnΠₙ neK)
                 (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢e'' (conv ⊢t ⊢A≡K) (un-univ:⇒*: D')))
                 cast~cast
[cast]Ne {A} {B} ⊢Γ (ne K D neK K≡K) (Indᵣ {i = i} D') {t} {e} [t] ⊢e =
  let [[ ⊢A , ⊢K , DK ]] = D
      ⊢A≡K = subset* DK
      [[ ⊢B , ⊢I , DI ]] = D'
      ⊢B≡I = subset* DI
      ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡I)))
      ⊢e'' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      cast~cast = ~-conv (~-castneInd K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ne′ K D neK K≡K) (reflEqTerm {l = ι ⁰} (ne′ K D neK K≡K) [t])) ⊢A≡K) ⊢e' ⊢e') (sym ⊢B≡I)
      ⊢t = escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]
  in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} (Indᵣ D') (castnIndₙ neK)
                 (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢e'' (conv ⊢t ⊢A≡K) (un-univ:⇒*: D')))
                 cast~cast

[castext]Ne : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩ne A ^[ ! , ⁰ ])
         ([A′] : Γ ⊩ne A′ ^[ ! , ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ ! , ι ⁰ ] / ne [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ ! , ι ⁰ ])
         (ShapeB : ShapeView Γ (ι ⁰) (ι ⁰) B B′ [ ! , ι ⁰ ] [ ! , ι ⁰ ] [B] [B′])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ ! , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ne [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ ! , ι ⁰ ] / ne [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ ! , ι ⁰ ] / ne [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (U ⁰) A′ B′ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ ! , ι ⁰ ] / [B])
[castext]Ne {A} {A′} {B} {B′} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡B′] [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [A] = ne K D neK K≡K
      [A′] = ne K′ D′ neK′ K′≡K′
      [[ ⊢A , ⊢K , DK ]] = D
      [[ ⊢A′ , ⊢K′ , DK′ ]] = D′
      ⊢A≡K = subset* DK
      [[ _ , ⊢M , DM ]] = D′′
      ⊢A'≡M = subset* DM
      [[ ⊢B , ⊢ℕ₁ , Dℕ₁ ]] = ℕA
      [[ ⊢B′ , ⊢ℕ₂ , Dℕ₂ ]] = ℕB
      ⊢B≡ℕ = subset* Dℕ₁
      ⊢B'≡ℕ = subset* Dℕ₂
      ⊢t = escapeTerm {l = ι ⁰} {A = A} (ne [A]) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} (ne [A′]) [t′]
      t≅t′ = escapeTermEq {l = ι ⁰} {A = A} (ne [A]) [t≡t′]
      ⊢eKB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      ⊢eKK₁ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡ℕ)))
      ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (refl (un-univ ⊢B′))))
      ⊢eMℕ = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (un-univ≡ ⊢B'≡ℕ)))
  in neuEqTerm:⇒*: {l = ι ⁰} (ℕᵣ ℕA) (castnℕₙ neK) (castnℕₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢eKB (conv ⊢t ⊢A≡K) (un-univ:⇒*: ℕA)))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B′ ⊢e′ (escapeTerm {l = ι ⁰} (ne [A′]) [t′]) (un-univ:⇒*: D′′)) (CastRedR*Term ⊢M neM ⊢e′' (conv ⊢t′ ⊢A'≡M) (un-univ:⇒*: ℕB))) (sym (≅-eq (escapeEq {l = ι ⁰} (ℕᵣ ℕA) [B≡B′]))))
                   (~-conv (~-castneℕ K≡M (≅-conv t≅t′ ⊢A≡K) ⊢eKK₁ ⊢eMℕ) (sym ⊢B≡ℕ))

[castext]Ne {A} {A′} {B} {B′} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [B≡B′] [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [A] = ne K D neK K≡K
      [A′] = ne K′ D′ neK′ K′≡K′
      [[ ⊢A , ⊢K , DK ]] = D
      [[ ⊢A′ , ⊢K′ , DK′ ]] = D′
      ⊢A≡K = subset* DK
      [[ _ , ⊢M , DM ]] = D′′
      ⊢A'≡M = subset* DM
      [[ ⊢B , ⊢ℕ₂₁ , Dℕ₂₁ ]] = ℕ2A
      [[ ⊢B′ , ⊢ℕ₂₂ , Dℕ₂₂ ]] = ℕ2B
      ⊢B≡ℕ2 = subset* Dℕ₂₁
      ⊢B'≡ℕ2 = subset* Dℕ₂₂
      ⊢t = escapeTerm {l = ι ⁰} {A = A} (ne [A]) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} (ne [A′]) [t′]
      t≅t′ = escapeTermEq {l = ι ⁰} {A = A} (ne [A]) [t≡t′]
      ⊢eKB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      ⊢eKK₁ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡ℕ2)))
      ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (refl (un-univ ⊢B′))))
      ⊢eMℕ2 = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (un-univ≡ ⊢B'≡ℕ2)))
  in neuEqTerm:⇒*: {l = ι ⁰} (ℕ2ᵣ ℕ2A) (castnℕ2ₙ neK) (castnℕ2ₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢eKB (conv ⊢t ⊢A≡K) (un-univ:⇒*: ℕ2A)))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B′ ⊢e′ (escapeTerm {l = ι ⁰} (ne [A′]) [t′]) (un-univ:⇒*: D′′)) (CastRedR*Term ⊢M neM ⊢e′' (conv ⊢t′ ⊢A'≡M) (un-univ:⇒*: ℕ2B))) (sym (≅-eq (escapeEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [B≡B′]))))
                   (~-conv (~-castneℕ2 K≡M (≅-conv t≅t′ ⊢A≡K) ⊢eKK₁ ⊢eMℕ2) (sym ⊢B≡ℕ2))

[castext]Ne {A} {A′} {B} {B′} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(ne′ K₁ D₁ neK₁ K≡K₁) .(ne′ K₂ D₂ neK₂ K≡K₂) (ne (ne K₁ D₁ neK₁ K≡K₁) (ne K₂ D₂ neK₂ K≡K₂)) (ne₌ M₁ D′₁ neM₁ K≡M₁) (neₜ k₁ [[ ⊢t , ⊢u , d₁ ]] (neNfₜ neK₃ ⊢k k≡k)) (neₜ k₂ [[ ⊢t′ , ⊢u′ , d₂ ]] (neNfₜ neK₄ ⊢k₁ k≡k₁)) (neₜ₌ k m d d′ (neNfₜ₌ neK₅ neM₂ k≡m)) ⊢e ⊢e′ =
  let [A′] = ne K′ D′ neK′ K′≡K′
      [B] = ne K₁ D₁ neK₁ K≡K₁
      [[ ⊢A , ⊢K , DK ]] = D
      [[ ⊢A′ , ⊢K′ , DK′ ]] = D′
      ⊢A≡K = subset* DK
      [[ _ , ⊢M , DM ]] = D′′
      ⊢A'≡M = subset* DM
      [[ ⊢B , ⊢K₁ , DK₁ ]] = D₁
      [[ ⊢B′ , ⊢K₂ , DK₂ ]] = D₂
      [[ _ , ⊢M' , DM' ]] = D′₁
      ⊢B'≡M' = subset* DM'
      ⊢B≡K₁ = subset* DK₁
      ⊢B≡K₂ = subset* DK₂
      ⊢A≡K′ = subset* DK′
      ⊢K′≡M = trans (sym ⊢A≡K′) ⊢A'≡M
      [t] = neₜ k₁ [[ ⊢t , ⊢u , d₁ ]] (neNfₜ neK₃ ⊢k k≡k)
      [t′] = neₜ k₂ [[ ⊢t′ , ⊢u′ , d₂ ]] (neNfₜ neK₄ ⊢k₁ k≡k₁)
      ⊢eKB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      ⊢eKK₁ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡K₁)))
      ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (refl (un-univ ⊢B′))))
      ⊢eMM₁ = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (un-univ≡ ⊢B'≡M')))
      PEk₁≡k = whrDet*Term (d₁ , ne neK₃) ( redₜ d , ne neK₅)
      k₁≡k = PE.subst (λ X → _ ⊢ k₁ ~ X ∷ K ^ [ ! , ι ⁰ ]) PEk₁≡k k≡k
      PEm≡k₂ = whrDet*Term (d₂ , ne neK₄) ( redₜ d′ , ne neM₂)
      m≡k₂ = PE.subst (λ X → _ ⊢ X ~ k₂ ∷ K′ ^ [ ! , ι ⁰ ]) PEm≡k₂ k≡k₁
      k₁≡k₂ = ~-trans (~-trans k₁≡k k≡m) (~-conv m≡k₂ (trans ⊢K′≡M (sym (≅-eq (~-to-≅ K≡M)))))
  in neuEqTerm:⇒*: {l = ι ⁰} (ne [B]) (castₙ neK neK₁ neK₃) (castₙ neM neM₁ neK₄)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D))
                   (transTerm:⇒:* (CastRedR*Term ⊢K neK ⊢eKB (conv ⊢t (univ (≅ₜ-eq (~-to-≅ₜ K≡K)))) (un-univ:⇒*: D₁))
                                  (conv:⇒*: (CastRedTerm*Term ⊢K neK ⊢K₁ neK₁ ⊢eKK₁ [[ ⊢t , ⊢u , d₁ ]]) (sym ⊢B≡K₁))))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B′ ⊢e′ (escapeTerm {l = ι ⁰} (ne [A′]) [t′]) (un-univ:⇒*: D′′))
                             (transTerm:⇒:* (CastRedR*Term ⊢M neM ⊢e′' (conv ⊢t′ ⊢K′≡M) (un-univ:⇒*: D′₁))
                                            (conv:⇒*: (CastRedTerm*Term ⊢M neM ⊢M' neM₁ ⊢eMM₁ (conv:⇒*: [[  ⊢t′ , ⊢u′ , d₂ ]] ⊢K′≡M)) (sym ⊢B'≡M'))))
                             (sym (≅-eq (escapeEq {l = ι ⁰} (ne [B]) (ne₌ M₁ D′₁ neM₁ K≡M₁)))))
                   (~-conv (~-cast K≡M K≡M₁ k₁≡k₂ ⊢eKK₁ ⊢eMM₁) (sym ⊢B≡K₁))


[castext]Ne {A} {A′} {B} {B′} {Γ} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(Πᵣ′ ! _ _ _ _ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) .(Πᵣ′ ! _ _ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
            (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
            (Π₌ F′ G′ D′₁ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [A] = ne K D neK K≡K
      [A′] = ne K′ D′ neK′ K′≡K′
      [B] = Πᵣ′ ! _ _ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext
      [[ ⊢A , ⊢K , DK ]] = D
      [[ ⊢A′ , ⊢K′ , DK′ ]] = D′
      ⊢A≡K = subset* DK
      [[ _ , ⊢M , DM ]] = D′′
      ⊢A'≡M = subset* DM
      [[ ⊢B , ⊢Π₁ , DΠ₁ ]] = D₁
      [[ ⊢B′ , ⊢Π₂ , DΠ₂ ]] = D₂
      ⊢B≡Π = subset* DΠ₁
      ⊢B'≡Π = subset* DΠ₂
      ⊢t = escapeTerm {l = ι ⁰} {A = A} (ne [A]) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} (ne [A′]) [t′]
      t≅t′ = escapeTermEq {l = ι ⁰} {A = A} (ne [A]) [t≡t′]
      ⊢eKB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      ⊢eKK₁ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡Π)))
      ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (refl (un-univ ⊢B′))))
      ⊢eMΠ = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B′))) (un-univ≡ ⊢A'≡M) (un-univ≡ ⊢B'≡Π)))
      Π≡Π = whrDet* (DΠ₂ , Whnf.Πₙ) (D′₁ , Whnf.Πₙ)
  in neuEqTerm:⇒*: {l = ι ⁰} [B] (castnΠₙ neK) (castnΠₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢eKB (conv ⊢t ⊢A≡K) (un-univ:⇒*: D₁)))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B′ ⊢e′ (escapeTerm {l = ι ⁰} (ne [A′]) [t′]) (un-univ:⇒*: D′′)) (CastRedR*Term ⊢M neM ⊢e′' (conv ⊢t′ ⊢A'≡M) (un-univ:⇒*: D₂))) (sym (≅-eq (escapeEq {l = ι ⁰} [B] (Π₌ F′ G′ D′₁ A≡B [F≡F′] [G≡G′])))))
                   (~-conv (~-castneΠ K≡M (≅-un-univ (PE.subst (λ X → Γ ⊢ Π F ^ ! ° ⁰ ▹ G ° ⁰ ° ⁰ ^ ! ≅ X ^ [ ! , ι ⁰ ]) (PE.sym Π≡Π) A≡B)) (≅-conv t≅t′ ⊢A≡K) ⊢eKK₁ ⊢eMΠ) (sym ⊢B≡Π))
[castext]Ne {A} {A′} {B} {B′} {Γ} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(Πᵣ′ _ _ _ _ _ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) .(Πᵣ′ _ _ _ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
            (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
            (Π₌ F′ G′ D′₁ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [A] = ne K D neK K≡K
      [A′] = ne K′ D′ neK′ K′≡K′
      [B] = Πᵣ′ % _ _ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext
      [[ ⊢A , ⊢K , DK ]] = D
      [[ ⊢A′ , ⊢K′ , DK′ ]] = D′
      ⊢A≡K = subset* DK
      [[ _ , ⊢M , DM ]] = D′′
      ⊢A'≡M = subset* DM
      [[ ⊢B , ⊢Π₁ , DΠ₁ ]] = D₁
      [[ ⊢B′ , ⊢Π₂ , DΠ₂ ]] = D₂
      ⊢B≡Π = subset* DΠ₁
      ⊢B'≡Π = subset* DΠ₂
      ⊢t = escapeTerm {l = ι ⁰} {A = A} (ne [A]) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} (ne [A′]) [t′]
      t≅t′ = escapeTermEq {l = ι ⁰} {A = A} (ne [A]) [t≡t′]
      ⊢eKB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      ⊢eKK₁ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡Π)))
      ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (refl (un-univ ⊢B′))))
      ⊢eMΠ = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B′))) (un-univ≡ ⊢A'≡M) (un-univ≡ ⊢B'≡Π)))
      Π≡Π = whrDet* (DΠ₂ , Whnf.Πₙ) (D′₁ , Whnf.Πₙ)
  in neuEqTerm:⇒*: {l = ι ⁰} [B] (castnΠₙ neK) (castnΠₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢eKB (conv ⊢t ⊢A≡K) (un-univ:⇒*: D₁)))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B′ ⊢e′ (escapeTerm {l = ι ⁰} (ne [A′]) [t′]) (un-univ:⇒*: D′′)) (CastRedR*Term ⊢M neM ⊢e′' (conv ⊢t′ ⊢A'≡M) (un-univ:⇒*: D₂))) (sym (≅-eq (escapeEq {l = ι ⁰} [B] (Π₌ F′ G′ D′₁ A≡B [F≡F′] [G≡G′])))))
                   (~-conv (~-castneΠ K≡M (≅-un-univ (PE.subst (λ X → Γ ⊢ Π F ^ % ° ⁰ ▹ G ° ⁰ ° ⁰ ^ ! ≅ X ^ [ ! , ι ⁰ ]) (PE.sym Π≡Π) A≡B)) (≅-conv t≅t′ ⊢A≡K) ⊢eKK₁ ⊢eMΠ) (sym ⊢B≡Π))
[castext]Ne {A} {A′} {B} {B′} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(Πᵣ′ _ _ _ _ _ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) .(Πᵣ′ _ _ _ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
            (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
            (Π₌ F′ G′ D′₁ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [[ ⊢B′ , ⊢Π₂ , DΠ₂ ]] = D₂
      Π≡Π = whrDet* (DΠ₂ , Whnf.Πₙ) (D′₁ , Whnf.Πₙ)
      _ , rF≡rF′ , _  = Π-PE-injectivity Π≡Π
  in ⊥-elim (!≢% rF≡rF′)
[castext]Ne {A} {A′} {B} {B′} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(Πᵣ′ _ _ _ _ _ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) .(Πᵣ′ _ _ _ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
            (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₂ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
            (Π₌ F′ G′ D′₁ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [[ ⊢B′ , ⊢Π₂ , DΠ₂ ]] = D₂
      Π≡Π = whrDet* (DΠ₂ , Whnf.Πₙ) (D′₁ , Whnf.Πₙ)
      _ , rF≡rF′ , _  = Π-PE-injectivity Π≡Π
  in ⊥-elim (!≢% (PE.sym rF≡rF′))
[castext]Ne {A} {A′} {B} {B′} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ IndA IndB) [B≡B′] [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [A] = ne K D neK K≡K
      [A′] = ne K′ D′ neK′ K′≡K′
      [[ ⊢A , ⊢K , DK ]] = D
      [[ ⊢A′ , ⊢K′ , DK′ ]] = D′
      ⊢A≡K = subset* DK
      [[ _ , ⊢M , DM ]] = D′′
      ⊢A'≡M = subset* DM
      [[ ⊢B , ⊢I₁ , DI₁ ]] = IndA
      [[ ⊢B′ , ⊢I₂ , DI₂ ]] = IndB
      ⊢B≡I = subset* DI₁
      ⊢B'≡I = subset* DI₂
      ⊢t = escapeTerm {l = ι ⁰} {A = A} (ne [A]) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} (ne [A′]) [t′]
      t≅t′ = escapeTermEq {l = ι ⁰} {A = A} (ne [A]) [t≡t′]
      ⊢eKB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (refl (un-univ ⊢B))))
      ⊢eKK₁ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡I)))
      ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (refl (un-univ ⊢B′))))
      ⊢eMI = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A'≡M) (un-univ≡ ⊢B'≡I)))
  in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ IndA) (castnIndₙ neK) (castnIndₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK ⊢eKB (conv ⊢t ⊢A≡K) (un-univ:⇒*: IndA)))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B′ ⊢e′ (escapeTerm {l = ι ⁰} (ne [A′]) [t′]) (un-univ:⇒*: D′′)) (CastRedR*Term ⊢M neM ⊢e′' (conv ⊢t′ ⊢A'≡M) (un-univ:⇒*: IndB))) (sym (≅-eq (escapeEq {l = ι ⁰} (Indᵣ IndA) [B≡B′]))))
                   (~-conv (~-castneInd K≡M (≅-conv t≅t′ ⊢A≡K) ⊢eKK₁ ⊢eMI) (sym ⊢B≡I))

[cast]ℕ : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩ℕ A)
         ([B] : Γ ⊩ℕ B) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ℕᵣ [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ ! ⁰) A B ^ [ % , ι ⁰ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / ℕᵣ [B]
[cast]ℕ {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢B , ⊢ℕ' , D' ]] {t} {e} (ℕₜ .(suc _) d n≡n (sucᵣ {a} x)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ (suc a) d n≡n (sucᵣ x))
      [N] = idRed:*: (univ (ℕⱼ ⊢Γ))
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      ⊢eℕB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (refl (un-univ ⊢B))))
      rec = [cast]ℕ ⊢Γ (idRed:*: ⊢ℕ) (idRed:*: ⊢ℕ) x ⊢eℕℕ
      cast≅cast = escapeTermEq {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕ)) (reflEqTerm {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕ)) rec)
  in ℕₜ (suc (cast ⁰ ℕ ℕ e a)) ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ (suc a) d n≡n (sucᵣ x))) (un-univ:⇒*: [[ ⊢A , ⊢ℕ , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ ⊢eℕB (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ' , D' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                  (CastRed*Termℕsuc ⊢eℕℕ (escapeTerm {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕ)) x))) (sym (subset* D'))))) (subset* D') ))
        (≅-suc-cong cast≅cast) (Natural-prop.sucᵣ rec)
[cast]ℕ {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢B , ⊢ℕ' , D' ]] {t} {e} (ℕₜ .zero d n≡n zeroᵣ) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ zero d n≡n zeroᵣ)
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
  in ℕₜ zero ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ zero d n≡n zeroᵣ)) (un-univ:⇒*: [[ ⊢A , ⊢ℕ , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ' , D' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                    (CastRed*Termℕzero ⊢eℕℕ)) (sym (subset* D'))))) (subset* D') ))
        (≅ₜ-zerorefl ⊢Γ) Natural-prop.zeroᵣ
[cast]ℕ {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢B , ⊢ℕ' , D' ]] {t} {e} (ℕₜ n d n≡n (ne x)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ n d n≡n (ne x))
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      neNfₜ nen ⊢n n~n = x
  in ℕₜ (cast ⁰ ℕ ℕ e n) ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ n d n≡n (ne x))) (un-univ:⇒*: [[ ⊢A , ⊢ℕ , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ' , D' ]])
                                                                  (conv:⇒*: (CastRed*Termℕℕ ⊢eℕℕ d) (sym (subset* D'))))) (subset* D') ))
        (~-to-≅ₜ (~-castℕℕ  n~n ⊢n ⊢n ⊢eℕℕ ⊢eℕℕ)) (ne (neNfₜ (castℕℕₙ nen) (castⱼ (ℕⱼ (wfTerm ⊢n)) (ℕⱼ (wfTerm ⊢n)) ⊢eℕℕ ⊢n) (~-castℕℕ n~n ⊢n ⊢n ⊢eℕℕ ⊢eℕℕ)))


[cast]ℕ2 : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩ℕ2 A)
         ([B] : Γ ⊩ℕ2 B) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ℕ2ᵣ [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ ! ⁰) A B ^ [ % , ι ⁰ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / ℕ2ᵣ [B]
[cast]ℕ2 {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ2 , D ]] [[ ⊢B , ⊢ℕ2' , D' ]] {t} {e} (ℕ2ₜ .(suc2 _) d n≡n (suc2ᵣ {a} x)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕ2ᵣ [[ ⊢A , ⊢ℕ2 , D ]]) (ℕ2ₜ (suc2 a) d n≡n (suc2ᵣ x))
      [N] = idRed:*: (univ (ℕ2ⱼ ⊢Γ))
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      ⊢eℕ2B = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (refl (un-univ ⊢B))))
      rec = [cast]ℕ2 ⊢Γ (idRed:*: ⊢ℕ2) (idRed:*: ⊢ℕ2) x ⊢eℕℕ
      cast≅cast = escapeTermEq {l = ι ⁰} (ℕ2ᵣ (idRed:*: ⊢ℕ2)) (reflEqTerm {l = ι ⁰} (ℕ2ᵣ (idRed:*: ⊢ℕ2)) rec)
  in ℕ2ₜ (suc2 (cast ⁰ ℕ2 ℕ2 e a)) ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ [[ ⊢A , ⊢ℕ2 , D ]]) (ℕ2ₜ (suc2 a) d n≡n (suc2ᵣ x))) (un-univ:⇒*: [[ ⊢A , ⊢ℕ2 , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 ⊢eℕ2B (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ2' , D' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕ2ℕ2 ⊢eℕℕ d)
                                                                  (CastRed*Termℕ2suc ⊢eℕℕ (escapeTerm {l = ι ⁰} (ℕ2ᵣ (idRed:*: ⊢ℕ2)) x))) (sym (subset* D'))))) (subset* D') ))
        (≅-suc2-cong cast≅cast) (suc2ᵣ rec)
[cast]ℕ2 {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ2 , D ]] [[ ⊢B , ⊢ℕ2' , D' ]] {t} {e} (ℕ2ₜ .zero2 d n≡n zero2ᵣ) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕ2ᵣ [[ ⊢A , ⊢ℕ2 , D ]]) (ℕ2ₜ zero2 d n≡n zero2ᵣ)
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
  in ℕ2ₜ zero2 ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ [[ ⊢A , ⊢ℕ2 , D ]]) (ℕ2ₜ zero2 d n≡n zero2ᵣ)) (un-univ:⇒*: [[ ⊢A , ⊢ℕ2 , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ2' , D' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕ2ℕ2 ⊢eℕℕ d)
                                                                    (CastRed*Termℕ2zero ⊢eℕℕ)) (sym (subset* D'))))) (subset* D') ))
        (≅ₜ-zero2refl ⊢Γ) zero2ᵣ
[cast]ℕ2 {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ2 , D ]] [[ ⊢B , ⊢ℕ2' , D' ]] {t} {e} (ℕ2ₜ n d n≡n (ne x)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕ2ᵣ [[ ⊢A , ⊢ℕ2 , D ]]) (ℕ2ₜ n d n≡n (ne x))
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      neNfₜ nen ⊢n n~n = x
  in ℕ2ₜ (cast ⁰ ℕ2 ℕ2 e n) ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ [[ ⊢A , ⊢ℕ2 , D ]]) (ℕ2ₜ n d n≡n (ne x))) (un-univ:⇒*: [[ ⊢A , ⊢ℕ2 , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ2' , D' ]])
                                                                  (conv:⇒*: (CastRed*Termℕ2ℕ2 ⊢eℕℕ d) (sym (subset* D'))))) (subset* D') ))
        (~-to-≅ₜ (~-castℕ2ℕ2  n~n ⊢n ⊢n ⊢eℕℕ ⊢eℕℕ)) (ne (neNfₜ (castℕ2ℕ2ₙ nen) (castⱼ (ℕ2ⱼ (wfTerm ⊢n)) (ℕ2ⱼ (wfTerm ⊢n)) ⊢eℕℕ ⊢n) (~-castℕ2ℕ2 n~n ⊢n ⊢n ⊢eℕℕ ⊢eℕℕ)))


[castext]ℕ : ∀ {A A' B B'  Γ}
             (⊢Γ : ⊢ Γ)
             ([A] : Γ ⊩ℕ A)
             ([A'] : Γ ⊩ℕ A')
             ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A' ^ [ ! , ι ⁰ ] / ℕᵣ [A])
             ([B] : Γ ⊩ℕ B)
             ([B'] : Γ ⊩ℕ B')
             ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B' ^ [ ! , ι ⁰ ] / ℕᵣ [B]) →
             ∀ {t t' e e' } → (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
                        → (⊢t′ : Γ ⊢ t' ∷ A' ^ [ ! , ι ⁰ ])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t' ∷ A ^ [ ! , ι ⁰ ] / ℕᵣ [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e' ∷ Id (U ⁰) A' B' ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ ! , ι ⁰ ] / ℕᵣ [B]
[castext]ℕ ⊢Γ [[ ⊢A , ⊢ℕA , DA ]] [[ ⊢A' , ⊢ℕA' , DA' ]] [A≡A′] [[ ⊢B , ⊢ℕB , DB ]] [[ ⊢B' , ⊢ℕB' , DB' ]] [B≡B′] {t} {t'} {e} {e'} ⊢t ⊢t′
              (ℕₜ₌ .(suc a) .(suc a') d d′ k≡k′ (sucᵣ {a} {a'} (ℕₜ₌ k k′ [[ ⊢a , ⊢u , d₁ ]] [[ ⊢a' , ⊢u₁ , d₂ ]] k≡k′₁ prop))) ⊢e ⊢e′ =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eℕℕ' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') )) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (ℕᵣ [[ ⊢B , ⊢ℕB , DB ]]) [B≡B′]
      rec = [castext]ℕ ⊢Γ (idRed:*: ⊢ℕA) (idRed:*: ⊢ℕA) (reflEq {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕA))) (idRed:*: ⊢ℕA) (idRed:*: ⊢ℕA) (reflEq {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕA)))
                       ⊢a ⊢a' (ℕₜ₌ k k′ [[ ⊢a , ⊢u , d₁ ]] [[ ⊢a' , ⊢u₁ , d₂ ]] k≡k′₁ prop) ⊢eℕℕ ⊢eℕℕ'
      cast≅cast = escapeTermEq {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕA)) rec
  in ℕₜ₌ (suc (cast ⁰ ℕ ℕ e a)) (suc (cast ⁰ ℕ ℕ e' a'))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕA , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕB , DB ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                  (CastRed*Termℕsuc ⊢eℕℕ ⊢a)) (sym (subset* DB))))) (subset* DB))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢ℕA' , DA' ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA'))
                                                                  (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕB' , DB' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ' d′)
                                                                  (CastRed*Termℕsuc ⊢eℕℕ' ⊢a')) (sym (subset* DB'))))) (subset* DB'))
         (≅-suc-cong cast≅cast) (sucᵣ rec)
[castext]ℕ ⊢Γ [[ ⊢A , ⊢ℕA , DA ]] [[ ⊢A' , ⊢ℕA' , DA' ]] [A≡A′] [[ ⊢B , ⊢ℕB , DB ]] [[ ⊢B' , ⊢ℕB' , DB' ]] [B≡B′] ⊢t ⊢t′ (ℕₜ₌ .zero .zero d d′ k≡k′ zeroᵣ) ⊢e ⊢e′ =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eℕℕ' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') )) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (ℕᵣ [[ ⊢B , ⊢ℕB , DB ]]) [B≡B′]
  in ℕₜ₌ zero zero
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕA , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕB , DB ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                    (CastRed*Termℕzero ⊢eℕℕ)) (sym (subset* DB))))) (subset* DB))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢ℕA' , DA' ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA'))
                                                                  (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕB' , DB' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ' d′)
                                                                    (CastRed*Termℕzero ⊢eℕℕ')) (sym (subset* DB'))))) (subset* DB'))
        (≅ₜ-zerorefl ⊢Γ) zeroᵣ
[castext]ℕ ⊢Γ [[ ⊢A , ⊢ℕA , DA ]] [[ ⊢A' , ⊢ℕA' , DA' ]] [A≡A′] [[ ⊢B , ⊢ℕB , DB ]] [[ ⊢B' , ⊢ℕB' , DB' ]] [B≡B′] ⊢t ⊢t′ (ℕₜ₌ k k′ d d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) ⊢e ⊢e′ =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eℕℕ' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') )) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (ℕᵣ [[ ⊢B , ⊢ℕB , DB ]]) [B≡B′]
  in neuEqTerm:⇒*: {l = ι ⁰} (ℕᵣ [[ ⊢B , ⊢ℕB , DB ]]) (castℕℕₙ neK) (castℕℕₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕA , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))(un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕB , DB ]])
                                                                  (conv:⇒*: (CastRed*Termℕℕ ⊢eℕℕ d) (sym (subset* DB)))))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢ℕA' , DA' ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') ))(un-univ≡ (subset* DA'))
                                                                  (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕB' , DB' ]])
                                                                  (conv:⇒*: (CastRed*Termℕℕ ⊢eℕℕ' d′) (sym (subset* DB'))))) (sym (≅-eq ⊢B≡B′)))
                   (~-conv (~-castℕℕ k≡m (_⊢_:⇒*:_∷_^_.⊢u d) (_⊢_:⇒*:_∷_^_.⊢u d′) ⊢eℕℕ ⊢eℕℕ') (sym (subset* DB)))


[castext]ℕ2 : ∀ {A A' B B'  Γ}
             (⊢Γ : ⊢ Γ)
             ([A] : Γ ⊩ℕ2 A)
             ([A'] : Γ ⊩ℕ2 A')
             ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A' ^ [ ! , ι ⁰ ] / ℕ2ᵣ [A])
             ([B] : Γ ⊩ℕ2 B)
             ([B'] : Γ ⊩ℕ2 B')
             ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B' ^ [ ! , ι ⁰ ] / ℕ2ᵣ [B]) →
             ∀ {t t' e e' } → (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
                        → (⊢t′ : Γ ⊢ t' ∷ A' ^ [ ! , ι ⁰ ])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t' ∷ A ^ [ ! , ι ⁰ ] / ℕ2ᵣ [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e' ∷ Id (U ⁰) A' B' ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ ! , ι ⁰ ] / ℕ2ᵣ [B]
[castext]ℕ2 ⊢Γ [[ ⊢A , ⊢ℕ2A , DA ]] [[ ⊢A' , ⊢ℕ2A' , DA' ]] [A≡A′] [[ ⊢B , ⊢ℕ2B , DB ]] [[ ⊢B' , ⊢ℕ2B' , DB' ]] [B≡B′] {t} {t'} {e} {e'} ⊢t ⊢t′
              (ℕ2ₜ₌ .(suc2 a) .(suc2 a') d d′ k≡k′ (suc2ᵣ {a} {a'} (ℕ2ₜ₌ k k′ [[ ⊢a , ⊢u , d₁ ]] [[ ⊢a' , ⊢u₁ , d₂ ]] k≡k′₁ prop))) ⊢e ⊢e′ =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eℕℕ' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') )) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (ℕ2ᵣ [[ ⊢B , ⊢ℕ2B , DB ]]) [B≡B′]
      rec = [castext]ℕ2 ⊢Γ (idRed:*: ⊢ℕ2A) (idRed:*: ⊢ℕ2A) (reflEq {l = ι ⁰} (ℕ2ᵣ (idRed:*: ⊢ℕ2A))) (idRed:*: ⊢ℕ2A) (idRed:*: ⊢ℕ2A) (reflEq {l = ι ⁰} (ℕ2ᵣ (idRed:*: ⊢ℕ2A)))
                       ⊢a ⊢a' (ℕ2ₜ₌ k k′ [[ ⊢a , ⊢u , d₁ ]] [[ ⊢a' , ⊢u₁ , d₂ ]] k≡k′₁ prop) ⊢eℕℕ ⊢eℕℕ'
      cast≅cast = escapeTermEq {l = ι ⁰} (ℕ2ᵣ (idRed:*: ⊢ℕ2A)) rec
  in ℕ2ₜ₌ (suc2 (cast ⁰ ℕ2 ℕ2 e a)) (suc2 (cast ⁰ ℕ2 ℕ2 e' a'))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕ2A , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕ2B , DB ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕ2ℕ2 ⊢eℕℕ d)
                                                                  (CastRed*Termℕ2suc ⊢eℕℕ ⊢a)) (sym (subset* DB))))) (subset* DB))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢ℕ2A' , DA' ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA'))
                                                                  (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕ2B' , DB' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕ2ℕ2 ⊢eℕℕ' d′)
                                                                  (CastRed*Termℕ2suc ⊢eℕℕ' ⊢a')) (sym (subset* DB'))))) (subset* DB'))
         (≅-suc2-cong cast≅cast) (suc2ᵣ rec)
[castext]ℕ2 ⊢Γ [[ ⊢A , ⊢ℕ2A , DA ]] [[ ⊢A' , ⊢ℕ2A' , DA' ]] [A≡A′] [[ ⊢B , ⊢ℕ2B , DB ]] [[ ⊢B' , ⊢ℕ2B' , DB' ]] [B≡B′] ⊢t ⊢t′ (ℕ2ₜ₌ .zero2 .zero2 d d′ k≡k′ zero2ᵣ) ⊢e ⊢e′ =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eℕℕ' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') )) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (ℕ2ᵣ [[ ⊢B , ⊢ℕ2B , DB ]]) [B≡B′]
  in ℕ2ₜ₌ zero2 zero2
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕ2A , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕ2B , DB ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕ2ℕ2 ⊢eℕℕ d)
                                                                    (CastRed*Termℕ2zero ⊢eℕℕ)) (sym (subset* DB))))) (subset* DB))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢ℕ2A' , DA' ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA'))
                                                                  (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕ2B' , DB' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕ2ℕ2 ⊢eℕℕ' d′)
                                                                    (CastRed*Termℕ2zero ⊢eℕℕ')) (sym (subset* DB'))))) (subset* DB'))
        (≅ₜ-zero2refl ⊢Γ) zero2ᵣ
[castext]ℕ2 ⊢Γ [[ ⊢A , ⊢ℕ2A , DA ]] [[ ⊢A' , ⊢ℕ2A' , DA' ]] [A≡A′] [[ ⊢B , ⊢ℕ2B , DB ]] [[ ⊢B' , ⊢ℕ2B' , DB' ]] [B≡B′] ⊢t ⊢t′ (ℕ2ₜ₌ k k′ d d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) ⊢e ⊢e′ =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eℕℕ' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') )) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (ℕ2ᵣ [[ ⊢B , ⊢ℕ2B , DB ]]) [B≡B′]
  in neuEqTerm:⇒*: {l = ι ⁰} (ℕ2ᵣ [[ ⊢B , ⊢ℕ2B , DB ]]) (castℕ2ℕ2ₙ neK) (castℕ2ℕ2ₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕ2A , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))(un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕ2B , DB ]])
                                                                  (conv:⇒*: (CastRed*Termℕ2ℕ2 ⊢eℕℕ d) (sym (subset* DB)))))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢ℕ2A' , DA' ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B') ))(un-univ≡ (subset* DA'))
                                                                  (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕ2B' , DB' ]])
                                                                  (conv:⇒*: (CastRed*Termℕ2ℕ2 ⊢eℕℕ' d′) (sym (subset* DB'))))) (sym (≅-eq ⊢B≡B′)))
                   (~-conv (~-castℕ2ℕ2 k≡m (_⊢_:⇒*:_∷_^_.⊢u d) (_⊢_:⇒*:_∷_^_.⊢u d′) ⊢eℕℕ ⊢eℕℕ') (sym (subset* DB)))

[cast]Ind : ∀ {A B i Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩Ind A ^ i)
         ([B] : Γ ⊩Ind B ^ i) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / Indᵣ [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ ! ⁰) A B ^ [ % , ι ⁰ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / Indᵣ [B]
[cast]Ind {A} {B} {i} {Γ} ⊢Γ [[ ⊢A , ⊢IndA , D ]] [[ ⊢B , ⊢IndB , D' ]] {t} {e}
  (Indₜ .(ctr i j args) d n≡n (ctrᵣ {j} {args} ps)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (Indᵣ [[ ⊢A , ⊢IndA , D ]]) (Indₜ (ctr i j args) d n≡n (ctrᵣ ps))
      ⊢eII = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      ⊢eIB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* D)) (refl (un-univ ⊢B))))
      ⊢args = inversion-Ctr (_⊢_:⇒*:_∷_^_.⊢u d)
      castArgs = castAll ps
      lens = PE.trans (length-map (λ a → cast ⁰ (Ind i) (Ind i) e a) args)
               (PE.trans (⊢All-length ⊢args) (length-map emb-stype (SU.ctrArgsTypeList i j)))
  in Indₜ (ctr i j (map (λ a → cast ⁰ (Ind i) (Ind i) e a) args))
         ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢IndA , D ]]))
                            (transTerm:⇒:* (CastRed*TermInd ⊢eIB (conv ⊢t (subset* D)) [[ ⊢B , ⊢IndB , D' ]])
                                           (conv:⇒*: (transTerm:⇒:* (CastRed*TermIndInd ⊢eII d)
                                           (CastRed*TermIndctr ⊢eII ⊢args)) (sym (subset* D'))))) (subset* D') ))
         (≅-ctr-cong ⊢Γ lens (≅AllInd ⊢Γ (reflAllInd castArgs)))
         (ctrᵣ castArgs)
  where
    castAll : ∀ {ts} → All (λ a → Γ ⊩Ind a ∷Ind i) ts
            → All (λ a → Γ ⊩Ind a ∷Ind i) (map (λ a → cast ⁰ (Ind i) (Ind i) e a) ts)
    castAll []ₐ = []ₐ
    castAll (p ∷ₐ rest) =
      ([cast]Ind ⊢Γ (idRed:*: ⊢IndA) (idRed:*: ⊢IndA) p
        (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))))
      ∷ₐ castAll rest

    ⊢All-length : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → length ts PE.≡ length As
    ⊢All-length εⱼ = PE.refl
    ⊢All-length (consⱼ _ rest) = PE.cong 1+ (⊢All-length rest)
[cast]Ind {A} {B} {i} {Γ} ⊢Γ [[ ⊢A , ⊢IndA , D ]] [[ ⊢B , ⊢IndB , D' ]] {t} {e}
  (Indₜ n d n≡n (ne x)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (Indᵣ [[ ⊢A , ⊢IndA , D ]]) (Indₜ n d n≡n (ne x))
      ⊢eII = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      neNfₜ nen ⊢n n~n = x
  in Indₜ (cast ⁰ (Ind i) (Ind i) e n)
         ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢IndA , D ]]))
                            (transTerm:⇒:* (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* D))
                                                           (refl (un-univ ⊢B))))) (conv ⊢t (subset* D)) [[ ⊢B , ⊢IndB , D' ]])
                                           (conv:⇒*: (CastRed*TermIndInd ⊢eII d) (sym (subset* D'))))) (subset* D') ))
         (~-to-≅ₜ (~-castIndInd n~n ⊢n ⊢n ⊢eII ⊢eII))
         (ne (neNfₜ (castIndIndₙ nen) (castⱼ (Indⱼ (wfTerm ⊢n)) (Indⱼ (wfTerm ⊢n)) ⊢eII ⊢n) (~-castIndInd n~n ⊢n ⊢n ⊢eII ⊢eII)))

[castext]Ind : ∀ {A A' B B' i Γ}
             (⊢Γ : ⊢ Γ)
             ([A] : Γ ⊩Ind A ^ i)
             ([A'] : Γ ⊩Ind A' ^ i)
             ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A' ^ [ ! , ι ⁰ ] / Indᵣ [A])
             ([B] : Γ ⊩Ind B ^ i)
             ([B'] : Γ ⊩Ind B' ^ i)
             ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B' ^ [ ! , ι ⁰ ] / Indᵣ [B]) →
             ∀ {t t' e e' } → (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
                        → (⊢t′ : Γ ⊢ t' ∷ A' ^ [ ! , ι ⁰ ])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t' ∷ A ^ [ ! , ι ⁰ ] / Indᵣ [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e' ∷ Id (U ⁰) A' B' ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ ! , ι ⁰ ] / Indᵣ [B]
[castext]Ind {i = i} {Γ = Γ} ⊢Γ [[ ⊢A , ⊢IndA , DA ]] [[ ⊢A' , ⊢IndA' , DA' ]] [A≡A′]
             [[ ⊢B , ⊢IndB , DB ]] [[ ⊢B' , ⊢IndB' , DB' ]] [B≡B′] {t} {t'} {e} {e'} ⊢t ⊢t′
             (Indₜ₌ .(ctr i j args) .(ctr i j args') d d′ k≡k′ (ctrᵣ {j} {args} {args'} ps)) ⊢e ⊢e′ =
  let ⊢eII = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eII' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢args = inversion-Ctr (_⊢_:⇒*:_∷_^_.⊢u d)
      ⊢args' = inversion-Ctr (_⊢_:⇒*:_∷_^_.⊢u d′)
      castArgs = castAll₂ ps
      lens = PE.trans (length-map (λ a → cast ⁰ (Ind i) (Ind i) e a) args)
               (PE.trans (⊢All-length ⊢args) (length-map emb-stype (SU.ctrArgsTypeList i j)))
  in Indₜ₌ (ctr i j (map (λ a → cast ⁰ (Ind i) (Ind i) e a) args))
           (ctr i j (map (λ a → cast ⁰ (Ind i) (Ind i) e' a) args'))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢IndA , DA ]]))
                            (transTerm:⇒:* (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA))
                                                           (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢IndB , DB ]])
                                           (conv:⇒*: (transTerm:⇒:* (CastRed*TermIndInd ⊢eII d)
                                           (CastRed*TermIndctr ⊢eII ⊢args)) (sym (subset* DB))))) (subset* DB))
         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢IndA' , DA' ]]))
                            (transTerm:⇒:* (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA'))
                                                           (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢IndB' , DB' ]])
                                           (conv:⇒*: (transTerm:⇒:* (CastRed*TermIndInd ⊢eII' d′)
                                           (CastRed*TermIndctr ⊢eII' ⊢args')) (sym (subset* DB'))))) (subset* DB'))
         (≅-ctr-cong ⊢Γ lens (≅AllInd ⊢Γ castArgs))
         (ctrᵣ castArgs)
  where
    castAll₂ : ∀ {ts ts'} → All₂ (λ a a' → Γ ⊩Ind a ≡ a' ∷Ind i) ts ts'
             → All₂ (λ a a' → Γ ⊩Ind a ≡ a' ∷Ind i)
                    (map (λ a → cast ⁰ (Ind i) (Ind i) e a) ts)
                    (map (λ a → cast ⁰ (Ind i) (Ind i) e' a) ts')
    castAll₂ []ₐ = []ₐ
    castAll₂ (Indₜ₌ k k′ [[ ⊢a , ⊢u , d₁ ]] [[ ⊢a' , ⊢u₁ , d₂ ]] k≡k′₁ prop ∷ₐ rest) =
      ([castext]Ind ⊢Γ (idRed:*: ⊢IndA) (idRed:*: ⊢IndA) (reflEq {l = ι ⁰} (Indᵣ (idRed:*: ⊢IndA)))
                   (idRed:*: ⊢IndA) (idRed:*: ⊢IndA) (reflEq {l = ι ⁰} (Indᵣ (idRed:*: ⊢IndA)))
                   ⊢a ⊢a' (Indₜ₌ k k′ [[ ⊢a , ⊢u , d₁ ]] [[ ⊢a' , ⊢u₁ , d₂ ]] k≡k′₁ prop)
                   (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB)))))
                   (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))))
      ∷ₐ castAll₂ rest

    ⊢All-length : ∀ {Γ ts As r} → Γ ⊢All ts ∷ As ^ r → length ts PE.≡ length As
    ⊢All-length εⱼ = PE.refl
    ⊢All-length (consⱼ _ rest) = PE.cong 1+ (⊢All-length rest)
[castext]Ind {i = i} ⊢Γ [[ ⊢A , ⊢IndA , DA ]] [[ ⊢A' , ⊢IndA' , DA' ]] [A≡A′]
             [[ ⊢B , ⊢IndB , DB ]] [[ ⊢B' , ⊢IndB' , DB' ]] [B≡B′] ⊢t ⊢t′
             (Indₜ₌ k k′ d d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) ⊢e ⊢e′ =
  let ⊢eII = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢eII' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (Indᵣ [[ ⊢B , ⊢IndB , DB ]]) [B≡B′]
  in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ [[ ⊢B , ⊢IndB , DB ]]) (castIndIndₙ neK) (castIndIndₙ neM)
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢IndA , DA ]]))
                            (transTerm:⇒:* (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA))
                                                           (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢IndB , DB ]])
                                           (conv:⇒*: (CastRed*TermIndInd ⊢eII d) (sym (subset* DB)))))
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A' , ⊢IndA' , DA' ]]))
                            (transTerm:⇒:* (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA'))
                                                           (refl (un-univ ⊢B'))))) (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢IndB' , DB' ]])
                                           (conv:⇒*: (CastRed*TermIndInd ⊢eII' d′) (sym (subset* DB'))))) (sym (≅-eq ⊢B≡B′)))
                   (~-conv (~-castIndInd k≡m (_⊢_:⇒*:_∷_^_.⊢u d) (_⊢_:⇒*:_∷_^_.⊢u d′) ⊢eII ⊢eII') (sym (subset* DB)))

[castext]ℕℕ2 : ∀ {A A' B B' Γ}
             (⊢Γ : ⊢ Γ)
             ([A] : Γ ⊩ℕ A)
             ([A'] : Γ ⊩ℕ A')
             ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A' ^ [ ! , ι ⁰ ] / ℕᵣ [A])
             ([B] : Γ ⊩ℕ2 B)
             ([B'] : Γ ⊩ℕ2 B')
             ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B' ^ [ ! , ι ⁰ ] / ℕ2ᵣ [B]) →
             ∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ℕᵣ [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A' ^ [ ! , ι ⁰ ] / ℕᵣ [A'])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ ! , ι ⁰ ] / ℕᵣ [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (U ⁰) A' B' ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e′ t′ ∷ B ^ [ ! , ι ⁰ ] / ℕ2ᵣ [B]
[castext]ℕℕ2 ⊢Γ natA natA' [A≡A′] nat2B nat2B' [B≡B′] {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [[ ⊢A , ⊢ℕA , DA ]] = natA
      [[ ⊢A' , ⊢ℕA' , DA' ]] = natA'
      [[ ⊢B , ⊢ℕ2B , DB ]] = nat2B
      [[ ⊢B' , ⊢ℕ2B' , DB' ]] = nat2B'
      ⊢t = escapeTerm {l = ι ⁰} (ℕᵣ natA) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} (ℕᵣ natA') [t′]
      ⊢eℕℕ2 = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢e′ℕℕ2 = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢eℕB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (refl (un-univ ⊢B))))
      ⊢e′ℕB′ = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA')) (refl (un-univ ⊢B'))))
      [ℕ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))
      [ℕ2] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Γ)))
      [Π] = ERd.Πℕℕ2 ⊢Γ
      [fwd] = ERd.EquivRed.[fwd] (equivRed) ⊢Γ
      [A≡ℕ] = id (univ (ℕⱼ ⊢Γ))
      [tℕ] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natA) [ℕ] [A≡ℕ] [t]
      [t′ℕ] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natA') [ℕ] [A≡ℕ] [t′]
      [t≡t′ℕ] = convEqTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natA) [ℕ] [A≡ℕ] [t≡t′]
      [fwd∘t] = appTerm PE.refl [ℕ] [ℕ2] [Π] [fwd] [tℕ]
      [fwd∘t′] = appTerm PE.refl [ℕ] [ℕ2] [Π] [fwd] [t′ℕ]
      [fwd∘t≡fwd∘t′] = app-congTerm [ℕ] [ℕ2] [Π] (reflEqTerm [Π] [fwd]) [tℕ] [t′ℕ] [t≡t′ℕ]
      [castℕℕ2] = proj₁ (redSubstTerm (cast-equiv-fwd ⊢eℕℕ2 (conv ⊢t (subset* DA))) [ℕ2] [fwd∘t])
      [castℕℕ2′] = proj₁ (redSubstTerm (cast-equiv-fwd ⊢e′ℕℕ2 (conv ⊢t′ (subset* DA'))) [ℕ2] [fwd∘t′])
      [castLit≡] = redSubst*EqTerm
        (cast-equiv-fwd ⊢eℕℕ2 (conv ⊢t (subset* DA)) ⇨ id (escapeTerm [ℕ2] [fwd∘t]))
        (cast-equiv-fwd ⊢e′ℕℕ2 (conv ⊢t′ (subset* DA')) ⇨ id (escapeTerm [ℕ2] [fwd∘t′]))
        [ℕ2] [ℕ2] (reflEq [ℕ2])
        [fwd∘t] [fwd∘t′] [fwd∘t≡fwd∘t′]
      [castAtB] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2B) [ℕ2] (id (univ (ℕ2ⱼ ⊢Γ))) [castℕℕ2]
      [castAtB'] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2B') [ℕ2] (id (univ (ℕ2ⱼ ⊢Γ))) [castℕℕ2′]
      [castAtB≡castAtB'] = convEqTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2B) (ℕ2ᵣ nat2B') [B≡B′]
        (convEqTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2B) [ℕ2] (id (univ (ℕ2ⱼ ⊢Γ))) [castLit≡])
      chainL = redₜ (transTerm:⇒:*
        (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: natA))
        (CastRed*Termℕ ⊢eℕB (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕ2B , DB ]]))
      chainR = redₜ (transTerm:⇒:*
        (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: natA'))
        (CastRed*Termℕ ⊢e′ℕB′ (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕ2B' , DB' ]]))
  in redSubst*EqTerm {l = ι ⁰} {ll = ι ⁰} chainL chainR (ℕ2ᵣ nat2B) (ℕ2ᵣ nat2B') [B≡B′]
                     [castAtB] [castAtB'] [castAtB≡castAtB']

[castext]ℕ2ℕ : ∀ {A A' B B' Γ}
             (⊢Γ : ⊢ Γ)
             ([A] : Γ ⊩ℕ2 A)
             ([A'] : Γ ⊩ℕ2 A')
             ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A' ^ [ ! , ι ⁰ ] / ℕ2ᵣ [A])
             ([B] : Γ ⊩ℕ B)
             ([B'] : Γ ⊩ℕ B')
             ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B' ^ [ ! , ι ⁰ ] / ℕᵣ [B]) →
             ∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ℕ2ᵣ [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A' ^ [ ! , ι ⁰ ] / ℕ2ᵣ [A'])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ ! , ι ⁰ ] / ℕ2ᵣ [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (U ⁰) A' B' ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e′ t′ ∷ B ^ [ ! , ι ⁰ ] / ℕᵣ [B]
[castext]ℕ2ℕ ⊢Γ nat2A nat2A' [A≡A′] natB natB' [B≡B′] {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let [[ ⊢A , ⊢ℕ2A , DA ]] = nat2A
      [[ ⊢A' , ⊢ℕ2A' , DA' ]] = nat2A'
      [[ ⊢B , ⊢ℕB , DB ]] = natB
      [[ ⊢B' , ⊢ℕB' , DB' ]] = natB'
      ⊢t = escapeTerm {l = ι ⁰} (ℕ2ᵣ nat2A) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} (ℕ2ᵣ nat2A') [t′]
      ⊢eℕ2ℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢e′ℕ2ℕ = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA')) (un-univ≡ (subset* DB'))))
      ⊢eℕ2A = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (refl (un-univ ⊢B))))
      ⊢e′ℕ2A′ = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢B'))) (un-univ≡ (subset* DA')) (refl (un-univ ⊢B'))))
      [ℕ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))
      [ℕ2] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Γ)))
      [Π] = ERd.Πℕ2ℕ ⊢Γ
      [bwd] = ERd.EquivRed.[bwd] (equivRed) ⊢Γ
      [A≡ℕ2] = id (univ (ℕ2ⱼ ⊢Γ))
      [tℕ2] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2A) [ℕ2] [A≡ℕ2] [t]
      [t′ℕ2] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2A') [ℕ2] [A≡ℕ2] [t′]
      [t≡t′ℕ2] = convEqTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2A) [ℕ2] [A≡ℕ2] [t≡t′]
      [bwd∘t] = appTerm PE.refl [ℕ2] [ℕ] [Π] [bwd] [tℕ2]
      [bwd∘t′] = appTerm PE.refl [ℕ2] [ℕ] [Π] [bwd] [t′ℕ2]
      [bwd∘t≡bwd∘t′] = app-congTerm [ℕ2] [ℕ] [Π] (reflEqTerm [Π] [bwd]) [tℕ2] [t′ℕ2] [t≡t′ℕ2]
      [castℕ2ℕ] = proj₁ (redSubstTerm (cast-equiv-bwd ⊢eℕ2ℕ (conv ⊢t (subset* DA))) [ℕ] [bwd∘t])
      [castℕ2ℕ′] = proj₁ (redSubstTerm (cast-equiv-bwd ⊢e′ℕ2ℕ (conv ⊢t′ (subset* DA'))) [ℕ] [bwd∘t′])
      [castLit≡] = redSubst*EqTerm
        (cast-equiv-bwd ⊢eℕ2ℕ (conv ⊢t (subset* DA)) ⇨ id (escapeTerm [ℕ] [bwd∘t]))
        (cast-equiv-bwd ⊢e′ℕ2ℕ (conv ⊢t′ (subset* DA')) ⇨ id (escapeTerm [ℕ] [bwd∘t′]))
        [ℕ] [ℕ] (reflEq [ℕ])
        [bwd∘t] [bwd∘t′] [bwd∘t≡bwd∘t′]
      [castAtB] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natB) [ℕ] (id (univ (ℕⱼ ⊢Γ))) [castℕ2ℕ]
      [castAtB'] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natB') [ℕ] (id (univ (ℕⱼ ⊢Γ))) [castℕ2ℕ′]
      [castAtB≡castAtB'] = convEqTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natB) (ℕᵣ natB') [B≡B′]
        (convEqTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natB) [ℕ] (id (univ (ℕⱼ ⊢Γ))) [castLit≡])
      chainL = redₜ (transTerm:⇒:*
        (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: nat2A))
        (CastRed*Termℕ2 ⊢eℕ2A (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕB , DB ]]))
      chainR = redₜ (transTerm:⇒:*
        (CastRed*Term ⊢B' ⊢e′ ⊢t′ (un-univ:⇒*: nat2A'))
        (CastRed*Termℕ2 ⊢e′ℕ2A′ (conv ⊢t′ (subset* DA')) [[ ⊢B' , ⊢ℕB' , DB' ]]))
  in redSubst*EqTerm {l = ι ⁰} {ll = ι ⁰} chainL chainR (ℕᵣ natB) (ℕᵣ natB') [B≡B′]
                     [castAtB] [castAtB'] [castAtB≡castAtB']


[cast] : ∀ {A B Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
       → (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]) → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B])
       × (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ r , ι ⁰ ] / [B]) → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) B A ^ [ % , ι ⁰ ]) → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ∷ A ^ [ r , ι ⁰ ] / [A])
[castext] : ∀ {A A′ B B′ Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ r , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ r , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ r , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ r , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ r , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ r , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) A′ B′ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
       × (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ r , ι ⁰ ] / [B])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ B′ ^ [ r , ι ⁰ ] / [B′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) B A ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) B′ A′ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ≡ cast ⁰ B′ A′ e′ t′ ∷ A ^ [ r , ι ⁰ ] / [A])
[castextShape] : ∀ {A A′ B B′ Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ r , ι ⁰ ])
         (ShapeA : ShapeView Γ (ι ⁰) (ι ⁰) A A′ [ r , ι ⁰ ] [ r , ι ⁰ ] [A] [A′])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ r , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ r , ι ⁰ ])
         (ShapeB : ShapeView Γ (ι ⁰) (ι ⁰) B B′ [ r , ι ⁰ ] [ r , ι ⁰ ] [B] [B′])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ r , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ r , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ r , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) A′ B′ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
       × (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ r , ι ⁰ ] / [B])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ B′ ^ [ r , ι ⁰ ] / [B′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) B A ^ [ % , ι ⁰ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) B′ A′ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ≡ cast ⁰ B′ A′ e′ t′ ∷ A ^ [ r , ι ⁰ ] / [A])

[cast] ⊢Γ (ℕᵣ x) (ℕᵣ x₁) = (λ [t] ⊢e → [cast]ℕ ⊢Γ x x₁ [t] ⊢e) , (λ [t] ⊢e → [cast]ℕ ⊢Γ x₁ x [t] ⊢e)
[cast] {A} {B} {r = !} ⊢Γ (ℕᵣ natD) (ℕ2ᵣ nat2D) =
  (λ {t} {e} [t] ⊢e →
     let [[ ⊢A , ⊢ℕA , DA ]] = natD
         [[ ⊢B , ⊢ℕ2B , DB ]] = nat2D
         ⊢t = escapeTerm {l = ι ⁰} {A = A} (ℕᵣ natD) [t]
         ⊢eℕℕ2 = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
         ⊢eℕB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (refl (un-univ ⊢B))))
         [ℕ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))
         [ℕ2] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Γ)))
         [Π] = ERd.Πℕℕ2 ⊢Γ
         [fwd] = ERd.EquivRed.[fwd] (equivRed) ⊢Γ
         [A≡ℕ] = id (univ (ℕⱼ ⊢Γ))
         [tℕ] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natD) [ℕ] [A≡ℕ] [t]
         [fwd∘t] = appTerm PE.refl [ℕ] [ℕ2] [Π] [fwd] [tℕ]
         [castℕℕ2] = proj₁ (redSubstTerm (cast-equiv-fwd ⊢eℕℕ2 (conv ⊢t (subset* DA))) [ℕ2] [fwd∘t])
         [castAtB] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2D) [ℕ2] (id (univ (ℕ2ⱼ ⊢Γ))) [castℕℕ2]
         chain = transTerm:⇒:*
                   (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: natD))
                   (CastRed*Termℕ ⊢eℕB (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕ2B , DB ]])
     in proj₁ (redSubst*Term {l = ι ⁰} {ll = ι ⁰} (redₜ chain) (ℕ2ᵣ nat2D) [castAtB])) ,
  (λ {t} {e} [t] ⊢e →
     let [[ ⊢B , ⊢ℕ2B , DB ]] = nat2D
         [[ ⊢A , ⊢ℕA , DA ]] = natD
         ⊢t = escapeTerm {l = ι ⁰} {A = B} (ℕ2ᵣ nat2D) [t]
         ⊢eℕ2ℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (un-univ≡ (subset* DA))))
         ⊢eℕ2A = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (refl (un-univ ⊢A))))
         [ℕ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))
         [ℕ2] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Γ)))
         [Π] = ERd.Πℕ2ℕ ⊢Γ
         [bwd] = ERd.EquivRed.[bwd] (equivRed) ⊢Γ
         [B≡ℕ2] = id (univ (ℕ2ⱼ ⊢Γ))
         [tℕ2] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ nat2D) [ℕ2] [B≡ℕ2] [t]
         [bwd∘t] = appTerm PE.refl [ℕ2] [ℕ] [Π] [bwd] [tℕ2]
         [castℕ2ℕ] = proj₁ (redSubstTerm (cast-equiv-bwd ⊢eℕ2ℕ (conv ⊢t (subset* DB))) [ℕ] [bwd∘t])
         [castAtA] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ natD) [ℕ] (id (univ (ℕⱼ ⊢Γ))) [castℕ2ℕ]
         chain = transTerm:⇒:*
                   (CastRed*Term ⊢A ⊢e ⊢t (un-univ:⇒*: nat2D))
                   (CastRed*Termℕ2 ⊢eℕ2A (conv ⊢t (subset* DB)) [[ ⊢A , ⊢ℕA , DA ]])
     in proj₁ (redSubst*Term {l = ι ⁰} {ll = ι ⁰} (redₜ chain) (ℕᵣ natD) [castAtA]))
[cast] {A} {B} {r = !} ⊢Γ (ℕ2ᵣ x) (ℕᵣ x₁) =
  (λ {t} {e} [t] ⊢e →
     let [[ ⊢B , ⊢ℕ2B , DB ]] = x
         [[ ⊢A , ⊢ℕA , DA ]] = x₁
         ⊢t = escapeTerm {l = ι ⁰} {A = A} (ℕ2ᵣ x) [t]
         ⊢eℕ2ℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (un-univ≡ (subset* DA))))
         ⊢eℕ2A = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (refl (un-univ ⊢A))))
         [ℕ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))
         [ℕ2] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Γ)))
         [Π] = ERd.Πℕ2ℕ ⊢Γ
         [bwd] = ERd.EquivRed.[bwd] (equivRed) ⊢Γ
         [B≡ℕ2] = id (univ (ℕ2ⱼ ⊢Γ))
         [tℕ2] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ x) [ℕ2] [B≡ℕ2] [t]
         [bwd∘t] = appTerm PE.refl [ℕ2] [ℕ] [Π] [bwd] [tℕ2]
         [castℕ2ℕ] = proj₁ (redSubstTerm (cast-equiv-bwd ⊢eℕ2ℕ (conv ⊢t (subset* DB))) [ℕ] [bwd∘t])
         [castAtA] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ x₁) [ℕ] (id (univ (ℕⱼ ⊢Γ))) [castℕ2ℕ]
         chain = transTerm:⇒:*
                   (CastRed*Term ⊢A ⊢e ⊢t (un-univ:⇒*: x))
                   (CastRed*Termℕ2 ⊢eℕ2A (conv ⊢t (subset* DB)) [[ ⊢A , ⊢ℕA , DA ]])
     in proj₁ (redSubst*Term {l = ι ⁰} {ll = ι ⁰} (redₜ chain) (ℕᵣ x₁) [castAtA])) ,
  (λ {t} {e} [t] ⊢e →
     let [[ ⊢A , ⊢ℕA , DA ]] = x₁
         [[ ⊢B , ⊢ℕ2B , DB ]] = x
         ⊢t = escapeTerm {l = ι ⁰} {A = B} (ℕᵣ x₁) [t]
         ⊢eℕℕ2 = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
         ⊢eℕB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ (subset* DA)) (refl (un-univ ⊢B))))
         [ℕ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))
         [ℕ2] = ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Γ)))
         [Π] = ERd.Πℕℕ2 ⊢Γ
         [fwd] = ERd.EquivRed.[fwd] (equivRed) ⊢Γ
         [A≡ℕ] = id (univ (ℕⱼ ⊢Γ))
         [tℕ] = convTerm₁ {l = ι ⁰} {l′ = ι ⁰} (ℕᵣ x₁) [ℕ] [A≡ℕ] [t]
         [fwd∘t] = appTerm PE.refl [ℕ] [ℕ2] [Π] [fwd] [tℕ]
         [castℕℕ2] = proj₁ (redSubstTerm (cast-equiv-fwd ⊢eℕℕ2 (conv ⊢t (subset* DA))) [ℕ2] [fwd∘t])
         [castAtB] = convTerm₂ {l = ι ⁰} {l′ = ι ⁰} (ℕ2ᵣ x) [ℕ2] (id (univ (ℕ2ⱼ ⊢Γ))) [castℕℕ2]
         chain = transTerm:⇒:*
                   (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: x₁))
                   (CastRed*Termℕ ⊢eℕB (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕ2B , DB ]])
     in proj₁ (redSubst*Term {l = ι ⁰} {ll = ι ⁰} (redₜ chain) (ℕ2ᵣ x) [castAtB]))
[cast] ⊢Γ (ℕ2ᵣ x) (ℕ2ᵣ x₁) = (λ [t] ⊢e → [cast]ℕ2 ⊢Γ x x₁ [t] ⊢e) , (λ [t] ⊢e → [cast]ℕ2 ⊢Γ x₁ x [t] ⊢e)
[cast] {A} {B} ⊢Γ (ℕᵣ x) (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) =
  (λ {t} {e} [t] ⊢e → let ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                          ⊢B≡K = un-univ≡ (subset* D)
                          ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* Dx
                          ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'
                          ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ ⊢B≡K))
                      in neₜ (cast ⁰ ℕ K e t)
                          (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                          (neNfₜ (castℕₙ neK) (castⱼ (ℕⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢A≡ℕ (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castℕ (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ' ) ⊢e' ⊢e'))) ,
  λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕᵣ x) [t] ⊢e

[cast] {A} {B} ⊢Γ (ℕ2ᵣ x) (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) =
  (λ {t} {e} [t] ⊢e → let ⊢A≡ℕ2 = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                          ⊢B≡K = un-univ≡ (subset* D)
                          ⊢A≡ℕ2' = let [[ _ , _ , Dx ]] = x in subset* Dx
                          ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) ⊢A≡ℕ2'
                          ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ2 ⊢B≡K))
                      in neₜ (cast ⁰ ℕ2 K e t)
                          (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ2
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                          (neNfₜ (castℕ2ₙ neK) (castⱼ (ℕ2ⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢A≡ℕ2 (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castℕ2 (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕ2ᵣ x) (reflEqTerm {l = ι ⁰} (ℕ2ᵣ x) [t])) ⊢A≡ℕ2' ) ⊢e' ⊢e'))) ,
  λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕ2ᵣ x) [t] ⊢e

[cast] {A} {B} {r = .!} ⊢Γ (ℕ2ᵣ x) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) =
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡ℕ2 = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡ℕ2' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢B≡Π = un-univ≡ (subset* D)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) ⊢A≡ℕ2'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕ2ᵣ x) (reflEqTerm {l = ι ⁰} (ℕ2ᵣ x) [t])) ⊢A≡ℕ2'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ2 ⊢B≡Π))
        cast~cast = ~-castℕ2Π (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {t = cast ⁰ A B e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castℕ2Πₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ2
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D)))) ,
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡ℕ2 = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π (un-univ≡ ⊢A≡ℕ2)))
        cast~cast = ~-castΠℕ2 (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ∞} (ℕ2ᵣ x) castΠℕ2ₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡ℕ2)))

[cast] {A} {B} {r = .!} ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) (ℕ2ᵣ x) =
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡ℕ2 = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π (un-univ≡ ⊢A≡ℕ2)))
        cast~cast = ~-castΠℕ2 (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ∞} {t = cast ⁰ A B e t} (ℕ2ᵣ x) castΠℕ2ₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡ℕ2))) ,
   (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢A≡ℕ2 = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡ℕ2' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) ⊢A≡ℕ2'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕ2ᵣ x) (reflEqTerm {l = ι ⁰} (ℕ2ᵣ x) [t])) ⊢A≡ℕ2'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ2 ⊢B≡Π ))
        cast~cast = ~-castℕ2Π (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {t = cast ⁰ B A e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castℕ2Πₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ2
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D))))



[cast] {A} {B} {r = .!} ⊢Γ (ℕᵣ x) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) =
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢B≡Π = un-univ≡ (subset* D)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ ⊢B≡Π))
        cast~cast = ~-castℕΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {t = cast ⁰ A B e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castℕΠₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D)))) ,
  λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡ℕ = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π (un-univ≡ ⊢A≡ℕ)))
        cast~cast = ~-castΠℕ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ∞} (ℕᵣ x) castΠℕₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡ℕ))
[cast] {A} {B}  ⊢Γ (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕᵣ x) =
   (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕᵣ x) [t] ⊢e) ,
   (λ {t} {e} [t] ⊢e → let ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                           ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* Dx
                           ⊢B≡K = un-univ≡ (subset* D)
                           ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'
                           ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ ⊢B≡K))
                       in neₜ (cast ⁰ ℕ K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castℕₙ neK) (castⱼ (ℕⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢A≡ℕ (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castℕ (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ' ) ⊢e' ⊢e')))
[cast] {A} {B}  ⊢Γ (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕ2ᵣ x) =
   (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕ2ᵣ x) [t] ⊢e) ,
   (λ {t} {e} [t] ⊢e → let ⊢A≡ℕ2 = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                           ⊢A≡ℕ2' = let [[ _ , _ , Dx ]] = x in subset* Dx
                           ⊢B≡K = un-univ≡ (subset* D)
                           ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) ⊢A≡ℕ2'
                           ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ2 ⊢B≡K))
                       in neₜ (cast ⁰ ℕ2 K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ2
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castℕ2ₙ neK) (castⱼ (ℕ2ⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢A≡ℕ2 (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castℕ2 (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕ2ᵣ x) (reflEqTerm {l = ι ⁰} (ℕ2ᵣ x) [t])) ⊢A≡ℕ2' ) ⊢e' ⊢e')))
[cast] {r = !} ⊢Γ (ne x) (ne x₁) = (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ x (ne x₁) [t] ⊢e) , λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ x₁ (ne x) [t] ⊢e
[cast] {A} {B} {r = !} ⊢Γ (ne′ K [[ ⊢A , ⊢K , D ]] neK K≡K) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext)  =
  (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢A , ⊢K , D ]] neK K≡K) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t] ⊢e) ,
  (λ {t} {e} [t] ⊢e →  let ⊢B≡Π = un-univ≡ (subset* DΠ)
                           ⊢B≡Π' = subset* DΠ
                           ⊢A≡K = un-univ≡ (subset* D)
                           [Π] = Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext
                           ⊢t' = escapeTerm {l = ι ⁰} [Π] [t]
                           ⊢t = conv ⊢t' ⊢B≡Π'
                           ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π ⊢A≡K))
                       in neₜ (cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: [[ ⊢B , ⊢Π , DΠ ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castΠₙ neK) (castⱼ (Πⱼ (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ un-univ ⊢F ▹ un-univ ⊢G) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢B≡Π (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castΠ (≅-un-univ B≡B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = B} [Π] (reflEqTerm {l = ι ⁰} [Π] [t])) ⊢B≡Π' ) ⊢e' ⊢e')))
[cast] {A} {B} ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) (ℕᵣ x) =
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡ℕ = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π (un-univ≡ ⊢A≡ℕ)))
        cast~cast = ~-castΠℕ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ∞} {t = cast ⁰ A B e t} (ℕᵣ x) castΠℕₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡ℕ))) ,
   (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡ℕ ⊢B≡Π ))
        cast~cast = ~-castℕΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {t = cast ⁰ B A e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castℕΠₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D))))
[cast] {A} {B} {r = !} ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext) (ne′ K [[ ⊢A , ⊢K , D ]] neK K≡K) =
  (λ {t} {e} [t] ⊢e →  let ⊢B≡Π = un-univ≡ (subset* DΠ)
                           ⊢A≡K = un-univ≡ (subset* D)
                           ⊢B≡Π' = subset* DΠ
                           [Π] = Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext
                           ⊢t' = escapeTerm {l = ι ⁰} [Π] [t]
                           ⊢t = conv ⊢t' ⊢B≡Π'
                           ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π ⊢A≡K))
                       in neₜ (cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: [[ ⊢B , ⊢Π , DΠ ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castΠₙ neK) (castⱼ (Πⱼ (λ _ → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ un-univ ⊢F ▹ un-univ ⊢G) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢B≡Π (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castΠ (≅-un-univ B≡B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} [Π] (reflEqTerm {l = ι ⁰} [Π] [t])) ⊢B≡Π' ) ⊢e' ⊢e'))) ,
  (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢A , ⊢K , D ]] neK K≡K) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t] ⊢e)
[cast] {r = %} ⊢Γ [A] [B] = [cast]irr ⊢Γ [A] [B] , [cast]irr ⊢Γ [B] [A]
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [A] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A] (reflEqTerm {l = ι ⁰} [A] [t])) ⊢A≡Π
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡Π)))
        cast~cast = ~-conv (~-castΠΠ%! (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) ⊢t≡t ⊢e' ⊢e') (sym ⊢B≡Π)
    in neuTerm:⇒*: {t = cast ⁰ A B e t} [B]
                                  castΠΠ%!ₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: D))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t ⊢A≡Π) D₁)) cast~cast) ,
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [B] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [B] (reflEqTerm {l = ι ⁰} [B] [t])) ⊢B≡Π
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢B≡Π) (un-univ≡ ⊢A≡Π)))
        cast~cast = ~-conv (~-castΠΠ!% (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) ⊢t≡t ⊢e' ⊢e') (sym ⊢A≡Π)
    in neuTerm:⇒*: {t = cast ⁰ B A e t} [A]
                                  castΠΠ!%ₙ (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t (un-univ:⇒*: D₁))
                                                   (CastRed*TermΠ (un-univ ⊢F₁ ) (un-univ ⊢G₁) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡Π)
                                                                  (refl (un-univ ⊢A))))) (conv ⊢t ⊢B≡Π) D)) cast~cast)
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [A] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A] (reflEqTerm {l = ι ⁰} [A] [t])) ⊢A≡Π
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡Π)))
        cast~cast = ~-conv (~-castΠΠ!% (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) ⊢t≡t ⊢e' ⊢e') (sym ⊢B≡Π)
    in neuTerm:⇒*: {t = cast ⁰ A B e t} [B]
                                  castΠΠ!%ₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: D))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t ⊢A≡Π) D₁)) cast~cast) ,
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [B] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [B] (reflEqTerm {l = ι ⁰} [B] [t])) ⊢B≡Π
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) (un-univ≡ ⊢B≡Π) (un-univ≡ ⊢A≡Π)))
        cast~cast = ~-conv (~-castΠΠ%! (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) ⊢t≡t ⊢e' ⊢e') (sym ⊢A≡Π)
    in neuTerm:⇒*: {t = cast ⁰ B A e t} [A]
                                  castΠΠ%!ₙ (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t (un-univ:⇒*: D₁))
                                                   (CastRed*TermΠ (un-univ ⊢F₁ ) (un-univ ⊢G₁) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡Π)
                                                                  (refl (un-univ ⊢A))))) (conv ⊢t ⊢B≡Π) D)) cast~cast)
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  [cast]₁ , [cast]₂
  where
    module b₁ = cast-ΠΠ-lemmas ⊢Γ ⊢F [F] ⊢F₁ [F₁]
                               (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))
    module b₂ = cast-ΠΠ-lemmas ⊢Γ ⊢F₁ [F₁] ⊢F [F]
                               (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))

    [A] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
    [B] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)

    [cast]₁ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [A])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / [B]
    [cast]₁ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢e
                              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                                proj₁ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₁.[b] b₁.[bext]

    [cast]₂ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ ! , ι ⁰ ] / [B])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) B A ^ [ % , ι ⁰ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ∷ A ^ [ ! , ι ⁰ ] / [A]
    [cast]₂ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢e
                              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                                proj₂ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₂.[b] b₂.[bext]
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  [cast]₁ , [cast]₂
  where
    module b₁ = cast-ΠΠ-lemmas ⊢Γ ⊢F [F] ⊢F₁ [F₁]
                               (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))
    module b₂ = cast-ΠΠ-lemmas ⊢Γ ⊢F₁ [F₁] ⊢F [F]
                               (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))

    [A] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
    [B] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)

    [cast]₁ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [A])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / [B]
    [cast]₁ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢e
                              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                                proj₁ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₁.[b] b₁.[bext]

    [cast]₂ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ ! , ι ⁰ ] / [B])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) B A ^ [ % , ι ⁰ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ∷ A ^ [ ! , ι ⁰ ] / [A]
    [cast]₂ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢e
                              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                                proj₂ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₂.[b] b₂.[bext]

[cast] {A} {B} ⊢Γ (Indᵣ {i = i} x) (Indᵣ {i = i′} x₁) = go (i ≟ i′)
  where
    go : Nullary.Dec (i PE.≡ i′) → _
    go (Nullary.yes PE.refl) = (λ [t] ⊢e → [cast]Ind ⊢Γ x x₁ [t] ⊢e) , (λ [t] ⊢e → [cast]Ind ⊢Γ x₁ x [t] ⊢e)
    go (Nullary.no i≢i′) =
      (λ {t} {e} [t] ⊢e →
        let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
            ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* (red x)
            ⊢B≡I = let [[ _ , _ , Dy ]] = x₁ in un-univ≡ (subset* (red x₁))
            [[ ⊢B , _ , Dy ]] = x₁
            ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
            t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I'
            ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡I))
            cast~cast = ~-castIndInd≢ i≢i′ t≅t ⊢e' ⊢e'
        in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} {n = cast ⁰ (Ind i) (Ind i′) e t}
                       (Indᵣ x₁) (castIndInd≢ₙ {l = ⁰} {i} {i′} i≢i′)
                       (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                     (refl (un-univ ⊢B))))) ⊢t x₁))
                       (~-conv cast~cast (sym (subset* Dy)))) ,
      (λ {t} {e} [t] ⊢e →
        let i′≢i : i′ PE.≢ i
            i′≢i eq = i≢i′ (PE.sym eq)
            ⊢B≡I = let [[ _ , _ , Dy ]] = x₁ in un-univ≡ (subset* (red x₁))
            ⊢B≡I' = let [[ _ , _ , Dy ]] = x₁ in subset* (red x₁)
            [[ ⊢A , _ , Dx ]] = x
            ⊢A≡I = subset* Dx
            [[ ⊢B , _ , Dy ]] = x₁
            ⊢t' = escapeTerm {l = ι ⁰} {A = B} (Indᵣ x₁) [t]
            ⊢t = conv ⊢t' ⊢B≡I'
            t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Indᵣ x₁) (reflEqTerm {l = ι ⁰} (Indᵣ x₁) [t])) ⊢B≡I'
            ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡I (un-univ≡ ⊢A≡I)))
            cast~cast = ~-castIndInd≢ i′≢i t≅t ⊢e' ⊢e'
        in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ B A e t} {n = cast ⁰ (Ind i′) (Ind i) e t}
                       (Indᵣ x) (castIndInd≢ₙ {l = ⁰} {i′} {i} i′≢i)
                       (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: x₁))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡I
                                                     (refl (un-univ ⊢A))))) ⊢t x)) (refl ⊢A))
                       (~-conv cast~cast (sym ⊢A≡I)))

[cast] {A} {B} ⊢Γ (Indᵣ {i = i} x) (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) =
  (λ {t} {e} [t] ⊢e → let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                          ⊢B≡K = un-univ≡ (subset* D)
                          ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* Dx
                          ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
                          ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡K))
                      in neₜ (cast ⁰ (Ind i) K e t)
                          (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                          (neNfₜ (castIndₙ neK) (castⱼ (Indⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B)))
                                                     ⊢A≡I (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castInd (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I' ) ⊢e' ⊢e'))) ,
  λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (Indᵣ x) [t] ⊢e

[cast] {A} {B} {r = .!} ⊢Γ (Indᵣ {i = i} x) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) =
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢B≡Π = un-univ≡ (subset* D)
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡Π))
        cast~cast = ~-castIndΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {t = cast ⁰ A B e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castIndΠₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D)))) ,
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡I = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π (un-univ≡ ⊢A≡I)))
        cast~cast = ~-castΠInd (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ∞} (Indᵣ x) castΠIndₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡I)))

[cast] {A} {B} {r = .!} ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) (Indᵣ {i = i} x) =
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡I = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π (un-univ≡ ⊢A≡I)))
        cast~cast = ~-castΠInd (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ∞} {t = cast ⁰ A B e t} (Indᵣ x) castΠIndₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡I))) ,
   (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡Π ))
        cast~cast = ~-castIndΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {t = cast ⁰ B A e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castIndΠₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D))))

[cast] {A} {B} {r = .!} ⊢Γ (Indᵣ {i = i} x) (ℕᵣ y) =
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢B≡ℕ = un-univ≡ (subset* (red y))
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡ℕ))
        cast~cast = ~-castIndℕ t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} {n = cast ⁰ (Ind i) ℕ e t} (ℕᵣ y) (castIndℕₙ {l = ⁰} {i})
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                  (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                 (refl (un-univ ⊢B))))) ⊢t y))
                   (~-conv cast~cast (sym (subset* (red y))))) ,
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡ℕ = un-univ≡ (subset* (red y))
        ⊢B≡ℕ' = subset* (red y)
        [[ ⊢A , ⊢I , Dx ]] = x
        ⊢A≡I = subset* Dx
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t' = escapeTerm {l = ι ⁰} {A = B} (ℕᵣ y) [t]
        ⊢t = conv ⊢t' ⊢B≡ℕ'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕᵣ y) (reflEqTerm {l = ι ⁰} (ℕᵣ y) [t])) ⊢B≡ℕ'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ (un-univ≡ ⊢A≡I)))
        cast~cast = ~-castℕInd t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ B A e t} {n = cast ⁰ ℕ (Ind i) e t} (Indᵣ x) (castℕIndₙ {l = ⁰} {i})
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: y))
                                  (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ
                                                 (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢I , Dx ]])) (refl ⊢A))
                   (~-conv cast~cast (sym ⊢A≡I)))

[cast] {A} {B} {r = .!} ⊢Γ (ℕᵣ y) (Indᵣ {i = i} x) =
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡ℕ = un-univ≡ (subset* (red y))
        ⊢B≡ℕ' = subset* (red y)
        [[ ⊢A , ⊢I , Dx ]] = x
        ⊢A≡I = subset* Dx
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t' = escapeTerm {l = ι ⁰} {A = A} (ℕᵣ y) [t]
        ⊢t = conv ⊢t' ⊢B≡ℕ'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕᵣ y) (reflEqTerm {l = ι ⁰} (ℕᵣ y) [t])) ⊢B≡ℕ'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ (un-univ≡ ⊢A≡I)))
        cast~cast = ~-castℕInd t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} {n = cast ⁰ ℕ (Ind i) e t} (Indᵣ x) (castℕIndₙ {l = ⁰} {i})
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: y))
                                  (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ
                                                 (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢I , Dx ]])) (refl ⊢A))
                   (~-conv cast~cast (sym ⊢A≡I))) ,
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢B≡ℕ = un-univ≡ (subset* (red y))
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡ℕ))
        cast~cast = ~-castIndℕ t≅t ⊢e' ⊢e'
        neCast = castIndℕₙ {l = ⁰} {i = i} {e = e} {t = t}
        redCast = transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                  (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                 (refl (un-univ ⊢B))))) ⊢t y)
    in neuTerm:⇒*: {l = ι ⁰} (ℕᵣ y) neCast redCast (~-conv cast~cast (sym (subset* (red y)))))

[cast] {A} {B} {r = .!} ⊢Γ (Indᵣ {i = i} x) (ℕ2ᵣ y) =
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢B≡ℕ2 = un-univ≡ (subset* (red y))
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡ℕ2))
        cast~cast = ~-castIndℕ2 t≅t ⊢e' ⊢e'
        neCast = castIndℕ2ₙ {l = ⁰} {i = i} {e = e} {t = t}
        redCast = transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                  (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                 (refl (un-univ ⊢B))))) ⊢t y)
    in neuTerm:⇒*: {l = ι ⁰} (ℕ2ᵣ y) neCast redCast (~-conv cast~cast (sym (subset* (red y))))) ,
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡ℕ2 = un-univ≡ (subset* (red y))
        ⊢B≡ℕ2' = subset* (red y)
        [[ ⊢A , ⊢I , Dx ]] = x
        ⊢A≡I = subset* Dx
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t' = escapeTerm {l = ι ⁰} {A = B} (ℕ2ᵣ y) [t]
        ⊢t = conv ⊢t' ⊢B≡ℕ2'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕ2ᵣ y) (reflEqTerm {l = ι ⁰} (ℕ2ᵣ y) [t])) ⊢B≡ℕ2'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ2 (un-univ≡ ⊢A≡I)))
        cast~cast = ~-castℕ2Ind t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ B A e t} {n = cast ⁰ ℕ2 (Ind i) e t} (Indᵣ x) (castℕ2Indₙ {l = ⁰} {i = i})
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: y))
                                  (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ2
                                                 (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢I , Dx ]])) (refl ⊢A))
                   (~-conv cast~cast (sym ⊢A≡I)))

[cast] {A} {B} {r = .!} ⊢Γ (ℕ2ᵣ y) (Indᵣ {i = i} x) =
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡ℕ2 = un-univ≡ (subset* (red y))
        ⊢B≡ℕ2' = subset* (red y)
        [[ ⊢A , ⊢I , Dx ]] = x
        ⊢A≡I = subset* Dx
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t' = escapeTerm {l = ι ⁰} {A = A} (ℕ2ᵣ y) [t]
        ⊢t = conv ⊢t' ⊢B≡ℕ2'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕ2ᵣ y) (reflEqTerm {l = ι ⁰} (ℕ2ᵣ y) [t])) ⊢B≡ℕ2'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ2 (un-univ≡ ⊢A≡I)))
        cast~cast = ~-castℕ2Ind t≅t ⊢e' ⊢e'
    in neuTerm:⇒*: {l = ι ⁰} {t = cast ⁰ A B e t} {n = cast ⁰ ℕ2 (Ind i) e t} (Indᵣ x) (castℕ2Indₙ {l = ⁰} {i})
                   (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: y))
                                  (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢B≡ℕ2
                                                 (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢I , Dx ]])) (refl ⊢A))
                   (~-conv cast~cast (sym ⊢A≡I))) ,
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢B≡ℕ2 = un-univ≡ (subset* (red y))
        [[ ⊢B , ⊢N , Dy ]] = y
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I'
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡ℕ2))
        cast~cast = ~-castIndℕ2 t≅t ⊢e' ⊢e'
        neCast = castIndℕ2ₙ {l = ⁰} {i = i} {e = e} {t = t}
        redCast = transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                  (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                 (refl (un-univ ⊢B))))) ⊢t y)
    in neuTerm:⇒*: {l = ι ⁰} (ℕ2ᵣ y) neCast redCast (~-conv cast~cast (sym (subset* (red y)))))

[cast] {A} {B} ⊢Γ (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) (Indᵣ {i = i} x) =
   (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (Indᵣ x) [t] ⊢e) ,
   (λ {t} {e} [t] ⊢e → let ⊢A≡I = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                           ⊢A≡I' = let [[ _ , _ , Dx ]] = x in subset* Dx
                           ⊢B≡K = un-univ≡ (subset* D)
                           ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) ⊢A≡I'
                           ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I ⊢B≡K))
                       in neₜ (cast ⁰ (Ind i) K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B))) ⊢A≡I
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castIndₙ neK) (castⱼ (Indⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B)))
                                                     ⊢A≡I (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castInd (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Indᵣ x) (reflEqTerm {l = ι ⁰} (Indᵣ x) [t])) ⊢A≡I' ) ⊢e' ⊢e')))


[castextShape] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′]) =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₂ , Πₙ) (D₂′ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% (PE.sym rF≡rF′))

[castextShape] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₂ , Πₙ) (D₂′ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% rF≡rF′)

[castextShape] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ r1 .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ r2 .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  _ _
  (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₄ , Πₙ) (D₄′ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% rF≡rF′)

[castextShape] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ r1 .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ r2 .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  _ _
  (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₄ , Πₙ) (D₄′ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% (PE.sym rF≡rF′))

[castextShape] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  _ _
  (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
     ([castext]₁ , [castext]₂)
   where
      module b₁ = cast-ΠΠ-lemmas ⊢Γ ⊢F₁ [F₁] ⊢F₃ [F₃]
                                 (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ)) ([F₃] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) (reflEq ([F₃] [ρ] ⊢Δ))))
      module b₂ = cast-ΠΠ-lemmas ⊢Γ ⊢F₂ [F₂] ⊢F₄ [F₄]
                                 (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) (reflEq ([F₂] [ρ] ⊢Δ)) ([F₄] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) (reflEq ([F₄] [ρ] ⊢Δ))))
      module b₃ = cast-ΠΠ-lemmas ⊢Γ ⊢F₃ [F₃] ⊢F₁ [F₁]
                                 (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ)) ([F₃] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) (reflEq ([F₃] [ρ] ⊢Δ))))
      module b₄ = cast-ΠΠ-lemmas ⊢Γ ⊢F₄ [F₄] ⊢F₂ [F₂]
                                 (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) (reflEq ([F₂] [ρ] ⊢Δ)) ([F₄] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) (reflEq ([F₄] [ρ] ⊢Δ))))

      [A₁] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      [A₂] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
      [A₁≡A₂] = (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
      [A₃] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      [A₄] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
      [A₃≡A₄] = (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′])

      Π≡Π = whrDet* (D₂ , Whnf.Πₙ) (D₂′ , Whnf.Πₙ)
      F₂≡F₂′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π in x
      G₂≡G₂′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π in x
      Π≡Π′ = whrDet* (D₄ , Whnf.Πₙ) (D₄′ , Whnf.Πₙ)
      F₄≡F₄′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π′ in x
      G₄≡G₄′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π′ in x

      A₁≡A₂ = PE.subst₂ (λ X Y → Γ ⊢ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ° ⁰ ^ ! ≅ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]) (PE.sym F₂≡F₂′) (PE.sym G₂≡G₂′) A₁≡A₂′
      A₃≡A₄ = PE.subst₂ (λ X Y → Γ ⊢ Π F₃ ^ ! ° ⁰ ▹ G₃ ° ⁰ ° ⁰ ^ ! ≅ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]) (PE.sym F₄≡F₄′) (PE.sym G₄≡G₄′) A₃≡A₄′
      [F₁≡F₂] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ≡ wk ρ X ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                         (PE.sym F₂≡F₂′) [F₁≡F₂′]
      [F₃≡F₄] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₃ ≡ wk ρ X ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                         (PE.sym F₄≡F₄′) [F₃≡F₄′]
      [G₁≡G₂] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                                → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                                → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])
                         (PE.sym G₂≡G₂′) [G₁≡G₂′]
      [G₃≡G₄] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                                → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                                → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a])
                         (PE.sym G₄≡G₄′) [G₃≡G₄′]

      [b₁≡b₂] : ∀ {ρ Δ e₁₃ e₂₄ x₃ x₄} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e₁₃ ∷ Id (U ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ⁰ ])
          → (Δ ⊢ e₂₄ ∷ Id (U ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ⁰ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ ! , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ≡ x₄ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₁.b ρ e₁₃ x₃ ≡ b₂.b ρ e₂₄ x₄ ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ
      [b₁≡b₂] [ρ] ⊢Δ ⊢e₁₃ ⊢e₂₄ [x₃] [x₄] [x₃≡x₄] =
        let
          ⊢e₃₁ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₁] [ρ] ⊢Δ)))
            (un-univ (escape ([F₃] [ρ] ⊢Δ))) ⊢e₁₃
          ⊢e₄₂ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₂] [ρ] ⊢Δ)))
            (un-univ (escape ([F₄] [ρ] ⊢Δ))) ⊢e₂₄
        in proj₂ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ)) [x₃] [x₄] [x₃≡x₄] ⊢e₃₁ ⊢e₄₂

      [b₃≡b₄] : ∀ {ρ Δ e₃₁ e₄₂ x₁ x₂} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e₃₁ ∷ Id (U ⁰) (wk ρ F₃) (wk ρ F₁) ^ [ % , ι ⁰ ])
          → (Δ ⊢ e₄₂ ∷ Id (U ⁰) (wk ρ F₄) (wk ρ F₂) ^ [ % , ι ⁰ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x₁ ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₂ ∷ wk ρ F₂ ^ [ ! , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₁ ≡ x₂ ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₃.b ρ e₃₁ x₁ ≡ b₄.b ρ e₄₂ x₂ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ
      [b₃≡b₄] [ρ] ⊢Δ ⊢e₃₁ ⊢e₄₂ [x₁] [x₂] [x₁≡x₂] =
        let
          ⊢e₁₃ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₃] [ρ] ⊢Δ)))
            (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e₃₁
          ⊢e₂₄ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₄] [ρ] ⊢Δ)))
            (un-univ (escape ([F₂] [ρ] ⊢Δ))) ⊢e₄₂
        in proj₁ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ)) [x₁] [x₂] [x₁≡x₂] ⊢e₁₃ ⊢e₂₄

      [castext]₁ : (∀ {t₁ t₂ e₁₃ e₂₄} → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₂ ∷ A₂ ^ [ ! , ι ⁰ ] / [A₂])
                        → ([t₁≡t₂] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ≡ t₂ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → (⊢e₁₃ : Γ ⊢ e₁₃ ∷ Id (U ⁰) A₁ A₃ ^ [ % , ι ⁰ ])
                        → (⊢e₂₄ : Γ ⊢ e₂₄ ∷ Id (U ⁰) A₂ A₄ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₁ A₃ e₁₃ t₁ ≡ cast ⁰ A₂ A₄ e₂₄ t₂ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
      [castext]₁ {t₁} {t₂} {e₁₃} {e₂₄}
        (f₁ , [[ ⊢t₁ , ⊢f₁ , Df₁ ]] , funf₁ , f₁≡f₁ , [f₁ext] , [f₁])
        (f₂ , [[ ⊢t₂ , ⊢f₂ , Df₂ ]] , funf₂ , f₂≡f₂ , [f₂ext] , [f₂])
        (f₁′ , f₂′ , [[ _ , ⊢f₁′ , Df₁′ ]] , [[ _ , ⊢f₂′ , Df₂′ ]] , funf₁′ , funf₂′ , _ , _ , _ , [f₁′≡f₂′])
        ⊢e₁₃ ⊢e₂₄ =
          ( (lam F₃ ▹ g₁.g (step id) (var 0) ^ ⁰)
          , (lam F₄ ▹ g₂.g (step id) (var 0) ^ ⁰)
          , g₁.Dg
          , conv:* g₂.Dg (sym (≅-eq A₃≡A₄))
          , lamₙ
          , lamₙ
          , g₁≡g₂
          , g₁.[castΠΠ]
          , convTerm₂ [A₃] [A₄] [A₃≡A₄] g₂.[castΠΠ]
          , [g₁a≡g₂a] )
          where
            f₁≡f₁′ = whrDet*Term (Df₁ , functionWhnf funf₁) (Df₁′ , functionWhnf funf₁′)
            f₂≡f₂′ = whrDet*Term (Df₂ , functionWhnf funf₂) (Df₂′ , functionWhnf funf₂′)
            [f₁≡f₂] = PE.subst₂ (λ X Y → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ^  ⁰ ≡ wk ρ Y ∘ a ^ ⁰ ∷ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a]) (PE.sym f₁≡f₁′) (PE.sym f₂≡f₂′) [f₁′≡f₂′]

            open cast-ΠΠ-lemmas-3 ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
              ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
              ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
              ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
              A₁≡A₂ A₃≡A₄ [F₁≡F₂] [F₃≡F₄] [G₁≡G₂] [G₃≡G₄]
              ⊢e₁₃ ⊢e₂₄
              ⊢t₁ Df₁ [f₁ext] [f₁]
              ⊢t₂ Df₂ [f₂ext] [f₂]
              [f₁≡f₂]
              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                proj₁ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                proj₁ ([castext] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x₁] [x₂] [G₁x₁≡G₂x₂] [x₃] [x₄] [G₃x₃≡G₄x₄] →
                proj₁ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂]
                                    ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄]))
              b₁.[b] b₁.[bext] b₂.[b] b₂.[bext] [b₁≡b₂]

      [castext]₂ : (∀ {t₃ t₄ e₃₁ e₄₂} → ([t₃] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → ([t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₄ ∷ A₄ ^ [ ! , ι ⁰ ] / [A₄])
                        → ([t₃≡t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ≡ t₄ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → (⊢e₃₁ : Γ ⊢ e₃₁ ∷ Id (U ⁰) A₃ A₁ ^ [ % , ι ⁰ ])
                        → (⊢e₄₂ : Γ ⊢ e₄₂ ∷ Id (U ⁰) A₄ A₂ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₃ A₁ e₃₁ t₃ ≡ cast ⁰ A₄ A₂ e₄₂ t₄ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
      [castext]₂ {t₃} {t₄} {e₃₁} {e₄₂}
        (f₃ , [[ ⊢t₃ , ⊢f₃ , Df₃ ]] , funf₃ , f₃≡f₃ , [f₃ext] , [f₃])
        (f₄ , [[ ⊢t₄ , ⊢f₄ , Df₄ ]] , funf₄ , f₄≡f₄ , [f₄ext] , [f₄])
        (f₃′ , f₄′ , [[ _ , ⊢f₃′ , Df₃′ ]] , [[ _ , ⊢f₄′ , Df₄′ ]] , funf₃′ , funf₄′ , _ , _ , _ , [f₃′≡f₄′])
        ⊢e₃₁ ⊢e₄₂ =
          ( (lam F₁ ▹ g₁.g (step id) (var 0) ^ ⁰)
          , (lam F₂ ▹ g₂.g (step id) (var 0) ^ ⁰)
          , g₁.Dg
          , conv:* g₂.Dg (sym (≅-eq A₁≡A₂))
          , lamₙ
          , lamₙ
          , g₁≡g₂
          , g₁.[castΠΠ]
          , convTerm₂ [A₁] [A₂] [A₁≡A₂] g₂.[castΠΠ]
          , [g₁a≡g₂a] )
          where
            f₃≡f₃′ = whrDet*Term (Df₃ , functionWhnf funf₃) (Df₃′ , functionWhnf funf₃′)
            f₄≡f₄′ = whrDet*Term (Df₄ , functionWhnf funf₄) (Df₄′ , functionWhnf funf₄′)
            [f₃≡f₄] = PE.subst₂ (λ X Y → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ^ ⁰ ≡ wk ρ Y ∘ a ^ ⁰ ∷ wk (lift ρ) G₃ [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a]) (PE.sym f₃≡f₃′) (PE.sym f₄≡f₄′) [f₃′≡f₄′]

            open cast-ΠΠ-lemmas-3 ⊢Γ ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
              ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
              ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
              ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
              A₃≡A₄ A₁≡A₂ [F₃≡F₄] [F₁≡F₂] [G₃≡G₄] [G₁≡G₂]
              ⊢e₃₁ ⊢e₄₂
              ⊢t₃ Df₃ [f₃ext] [f₃]
              ⊢t₄ Df₄ [f₄ext] [f₄]
              [f₃≡f₄]
              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                proj₂ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                proj₂ ([castext] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x₃] [x₄] [G₃x₃≡G₄x₄] [x₁] [x₂] [G₁x₁≡G₂x₂] →
                proj₂ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂]
                                    ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄]))
              b₃.[b] b₃.[bext] b₄.[b] b₄.[bext] [b₃≡b₄]

[castextShape] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  _ _
  (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
     ([castext]₁ , [castext]₂)
   where
      module b₁ = cast-ΠΠ-lemmas ⊢Γ ⊢F₁ [F₁] ⊢F₃ [F₃]
                                 (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ)) ([F₃] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) (reflEq ([F₃] [ρ] ⊢Δ))))
      module b₂ = cast-ΠΠ-lemmas ⊢Γ ⊢F₂ [F₂] ⊢F₄ [F₄]
                                 (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) (reflEq ([F₂] [ρ] ⊢Δ)) ([F₄] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) (reflEq ([F₄] [ρ] ⊢Δ))))
      module b₃ = cast-ΠΠ-lemmas ⊢Γ ⊢F₃ [F₃] ⊢F₁ [F₁]
                                 (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ)) ([F₃] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) (reflEq ([F₃] [ρ] ⊢Δ))))
      module b₄ = cast-ΠΠ-lemmas ⊢Γ ⊢F₄ [F₄] ⊢F₂ [F₂]
                                 (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) (reflEq ([F₂] [ρ] ⊢Δ)) ([F₄] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) (reflEq ([F₄] [ρ] ⊢Δ))))

      [A₁] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      [A₂] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
      [A₁≡A₂] = (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
      [A₃] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      [A₄] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
      [A₃≡A₄] = (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′])

      Π≡Π = whrDet* (D₂ , Whnf.Πₙ) (D₂′ , Whnf.Πₙ)
      F₂≡F₂′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π in x
      G₂≡G₂′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π in x
      Π≡Π′ = whrDet* (D₄ , Whnf.Πₙ) (D₄′ , Whnf.Πₙ)
      F₄≡F₄′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π′ in x
      G₄≡G₄′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π′ in x

      A₁≡A₂ = PE.subst₂ (λ X Y → Γ ⊢ Π F₁ ^ % ° ⁰ ▹ G₁ ° ⁰ ° ⁰ ^ ! ≅ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]) (PE.sym F₂≡F₂′) (PE.sym G₂≡G₂′) A₁≡A₂′
      A₃≡A₄ = PE.subst₂ (λ X Y → Γ ⊢ Π F₃ ^ % ° ⁰ ▹ G₃ ° ⁰ ° ⁰ ^ ! ≅ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]) (PE.sym F₄≡F₄′) (PE.sym G₄≡G₄′) A₃≡A₄′
      [F₁≡F₂] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ≡ wk ρ X ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                         (PE.sym F₂≡F₂′) [F₁≡F₂′]
      [F₃≡F₄] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₃ ≡ wk ρ X ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                         (PE.sym F₄≡F₄′) [F₃≡F₄′]
      [G₁≡G₂] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                                → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                                → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])
                         (PE.sym G₂≡G₂′) [G₁≡G₂′]
      [G₃≡G₄] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                                → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                                → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a])
                         (PE.sym G₄≡G₄′) [G₃≡G₄′]

      [b₁≡b₂] : ∀ {ρ Δ e₁₃ e₂₄ x₃ x₄} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e₁₃ ∷ Id SProp (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ⁰ ])
          → (Δ ⊢ e₂₄ ∷ Id SProp (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ⁰ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ % , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ≡ x₄ ∷ wk ρ F₃ ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₁.b ρ e₁₃ x₃ ≡ b₂.b ρ e₂₄ x₄ ∷ wk ρ F₁ ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ
      [b₁≡b₂] [ρ] ⊢Δ ⊢e₁₃ ⊢e₂₄ [x₃] [x₄] [x₃≡x₄] =
        let
          ⊢e₃₁ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₁] [ρ] ⊢Δ)))
            (un-univ (escape ([F₃] [ρ] ⊢Δ))) ⊢e₁₃
          ⊢e₄₂ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₂] [ρ] ⊢Δ)))
            (un-univ (escape ([F₄] [ρ] ⊢Δ))) ⊢e₂₄
        in proj₂ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ)) [x₃] [x₄] [x₃≡x₄] ⊢e₃₁ ⊢e₄₂

      [b₃≡b₄] : ∀ {ρ Δ e₃₁ e₄₂ x₁ x₂} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e₃₁ ∷ Id SProp (wk ρ F₃) (wk ρ F₁) ^ [ % , ι ⁰ ])
          → (Δ ⊢ e₄₂ ∷ Id SProp (wk ρ F₄) (wk ρ F₂) ^ [ % , ι ⁰ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x₁ ∷ wk ρ F₁ ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₂ ∷ wk ρ F₂ ^ [ % , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₁ ≡ x₂ ∷ wk ρ F₁ ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₃.b ρ e₃₁ x₁ ≡ b₄.b ρ e₄₂ x₂ ∷ wk ρ F₃ ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ
      [b₃≡b₄] [ρ] ⊢Δ ⊢e₃₁ ⊢e₄₂ [x₁] [x₂] [x₁≡x₂] =
        let
          ⊢e₁₃ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₃] [ρ] ⊢Δ)))
            (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e₃₁
          ⊢e₂₄ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₄] [ρ] ⊢Δ)))
            (un-univ (escape ([F₂] [ρ] ⊢Δ))) ⊢e₄₂
        in proj₁ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ)) [x₁] [x₂] [x₁≡x₂] ⊢e₁₃ ⊢e₂₄

      [castext]₁ : (∀ {t₁ t₂ e₁₃ e₂₄} → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₂ ∷ A₂ ^ [ ! , ι ⁰ ] / [A₂])
                        → ([t₁≡t₂] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ≡ t₂ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → (⊢e₁₃ : Γ ⊢ e₁₃ ∷ Id (U ⁰) A₁ A₃ ^ [ % , ι ⁰ ])
                        → (⊢e₂₄ : Γ ⊢ e₂₄ ∷ Id (U ⁰) A₂ A₄ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₁ A₃ e₁₃ t₁ ≡ cast ⁰ A₂ A₄ e₂₄ t₂ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
      [castext]₁ {t₁} {t₂} {e₁₃} {e₂₄}
        (f₁ , [[ ⊢t₁ , ⊢f₁ , Df₁ ]] , funf₁ , f₁≡f₁ , [f₁ext] , [f₁])
        (f₂ , [[ ⊢t₂ , ⊢f₂ , Df₂ ]] , funf₂ , f₂≡f₂ , [f₂ext] , [f₂])
        (f₁′ , f₂′ , [[ _ , ⊢f₁′ , Df₁′ ]] , [[ _ , ⊢f₂′ , Df₂′ ]] , funf₁′ , funf₂′ , _ , _ , _ , [f₁′≡f₂′])
        ⊢e₁₃ ⊢e₂₄ =
          ( (lam F₃ ▹ g₁.g (step id) (var 0) ^ ⁰)
          , (lam F₄ ▹ g₂.g (step id) (var 0) ^ ⁰)
          , g₁.Dg
          , conv:* g₂.Dg (sym (≅-eq A₃≡A₄))
          , lamₙ
          , lamₙ
          , g₁≡g₂
          , g₁.[castΠΠ]
          , convTerm₂ [A₃] [A₄] [A₃≡A₄] g₂.[castΠΠ]
          , [g₁a≡g₂a] )
          where
            f₁≡f₁′ = whrDet*Term (Df₁ , functionWhnf funf₁) (Df₁′ , functionWhnf funf₁′)
            f₂≡f₂′ = whrDet*Term (Df₂ , functionWhnf funf₂) (Df₂′ , functionWhnf funf₂′)
            [f₁≡f₂] = PE.subst₂ (λ X Y → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ^ ⁰ ≡ wk ρ Y ∘ a ^ ⁰ ∷ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a]) (PE.sym f₁≡f₁′) (PE.sym f₂≡f₂′) [f₁′≡f₂′]

            open cast-ΠΠ-lemmas-3 ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
              ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
              ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
              ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
              A₁≡A₂ A₃≡A₄ [F₁≡F₂] [F₃≡F₄] [G₁≡G₂] [G₃≡G₄]
              ⊢e₁₃ ⊢e₂₄
              ⊢t₁ Df₁ [f₁ext] [f₁]
              ⊢t₂ Df₂ [f₂ext] [f₂]
              [f₁≡f₂]
              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                proj₁ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                proj₁ ([castext] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x₁] [x₂] [G₁x₁≡G₂x₂] [x₃] [x₄] [G₃x₃≡G₄x₄] →
                proj₁ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂]
                                    ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄]))
              b₁.[b] b₁.[bext] b₂.[b] b₂.[bext] [b₁≡b₂]

      [castext]₂ : (∀ {t₃ t₄ e₃₁ e₄₂} → ([t₃] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → ([t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₄ ∷ A₄ ^ [ ! , ι ⁰ ] / [A₄])
                        → ([t₃≡t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ≡ t₄ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → (⊢e₃₁ : Γ ⊢ e₃₁ ∷ Id (U ⁰) A₃ A₁ ^ [ % , ι ⁰ ])
                        → (⊢e₄₂ : Γ ⊢ e₄₂ ∷ Id (U ⁰) A₄ A₂ ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₃ A₁ e₃₁ t₃ ≡ cast ⁰ A₄ A₂ e₄₂ t₄ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
      [castext]₂ {t₃} {t₄} {e₃₁} {e₄₂}
        (f₃ , [[ ⊢t₃ , ⊢f₃ , Df₃ ]] , funf₃ , f₃≡f₃ , [f₃ext] , [f₃])
        (f₄ , [[ ⊢t₄ , ⊢f₄ , Df₄ ]] , funf₄ , f₄≡f₄ , [f₄ext] , [f₄])
        (f₃′ , f₄′ , [[ _ , ⊢f₃′ , Df₃′ ]] , [[ _ , ⊢f₄′ , Df₄′ ]] , funf₃′ , funf₄′ , _ , _ , _ , [f₃′≡f₄′])
        ⊢e₃₁ ⊢e₄₂ =
          ( (lam F₁ ▹ g₁.g (step id) (var 0) ^ ⁰)
          , (lam F₂ ▹ g₂.g (step id) (var 0) ^ ⁰)
          , g₁.Dg
          , conv:* g₂.Dg (sym (≅-eq A₁≡A₂))
          , lamₙ
          , lamₙ
          , g₁≡g₂
          , g₁.[castΠΠ]
          , convTerm₂ [A₁] [A₂] [A₁≡A₂] g₂.[castΠΠ]
          , [g₁a≡g₂a] )
          where
            f₃≡f₃′ = whrDet*Term (Df₃ , functionWhnf funf₃) (Df₃′ , functionWhnf funf₃′)
            f₄≡f₄′ = whrDet*Term (Df₄ , functionWhnf funf₄) (Df₄′ , functionWhnf funf₄′)
            [f₃≡f₄] = PE.subst₂ (λ X Y → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ^ ⁰ ≡ wk ρ Y ∘ a ^ ⁰ ∷ wk (lift ρ) G₃ [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a]) (PE.sym f₃≡f₃′) (PE.sym f₄≡f₄′) [f₃′≡f₄′]

            open cast-ΠΠ-lemmas-3 ⊢Γ ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
              ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
              ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
              ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
              A₃≡A₄ A₁≡A₂ [F₃≡F₄] [F₁≡F₂] [G₃≡G₄] [G₁≡G₂]
              ⊢e₃₁ ⊢e₄₂
              ⊢t₃ Df₃ [f₃ext] [f₃]
              ⊢t₄ Df₄ [f₄ext] [f₄]
              [f₃≡f₄]
              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                proj₂ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                proj₂ ([castext] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x₃] [x₄] [G₃x₃≡G₄x₄] [x₁] [x₂] [G₁x₁≡G₂x₂] →
                proj₂ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂]
                                    ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄]))
              b₃.[b] b₃.[bext] b₄.[b] b₄.[bext] [b₃≡b₄]


[castextShape] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  _ _
  (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [A₁] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        [A₃] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
        [A₂] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
        ⊢t = escapeTerm [A₁] [t]
        ⊢t′ = escapeTerm [A₂] [t′]
        ⊢A₁≡Π = subset* D₁
        ⊢A₃≡Π = subset* D₃
        ⊢A₂≡Π = subset* D₂
        ⊢A₄≡Π = subset* D₄
        ⊢A₃≡A₄ = escapeEq {l = ι ⁰} [A₃] (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′])
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A₁] [t≡t′]) ⊢A₁≡Π
        ΠFG′≡ΠFG′₂ = whrDet* (D₂ , Πₙ) (D₂′ , Πₙ)
        F′≡F′₂ , _ , _ , G′≡G′₂ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₂
        ΠFG′≡ΠFG′₄ = whrDet* (D₄ , Πₙ) (D₄′ , Πₙ)
        F′≡F′₄ , _ , _ , G′≡G′₄ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₄
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁))) (un-univ≡ ⊢A₁≡Π) (un-univ≡ ⊢A₃≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₂ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₂ ⊢A₂≡Π))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₄ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₄ ⊢A₄≡Π))))
        cast~cast = ~-conv (~-castΠΠ!% (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₂′) (un-univ ⊢F₃) (un-univ ⊢G₃) (≅-un-univ A₃≡A₄′) ⊢t≡t ⊢e' ⊢e′') (sym ⊢A₃≡Π)
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ° ⁰ ^ !) (Π F₃ ^ % ° ⁰ ▹ G₃ ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ (Π F₂ ^ ! ° ⁰ ▹ G₂ ° ⁰ ° ⁰ ^ !)  (Π F₄ ^ % ° ⁰ ▹ G₄ ° ⁰ ° ⁰ ^ !) e′ t′}
                     [A₃]
                     castΠΠ!%ₙ castΠΠ!%ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A₃ ⊢e ⊢t (un-univ:⇒*: [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₁ ) (un-univ ⊢G₁) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₃) )) (un-univ≡ ⊢A₁≡Π)
                                                                  (refl (un-univ ⊢A₃))))) (conv ⊢t ⊢A₁≡Π) [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A₄ ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₂ ) (un-univ ⊢G₂) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₄) )) (un-univ≡ ⊢A₂≡Π)
                                                                  (refl (un-univ ⊢A₄))))) (conv ⊢t′ ⊢A₂≡Π) [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]])) (sym (≅-eq ⊢A₃≡A₄)))
                      (~-irrelevanceTerm PE.refl PE.refl (PE.cong₄ (λ X Y X' Y' → cast ⁰ (Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π X' ^ % ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₂) (PE.sym G′≡G′₂) (PE.sym F′≡F′₄) (PE.sym G′≡G′₄)) cast~cast)),
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [A₁] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        [A₃] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
        [A₄] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
        ⊢t = escapeTerm [A₃] [t]
        ⊢t′ = escapeTerm [A₄] [t′]
        ⊢A₁≡Π = subset* D₁
        ⊢A₃≡Π = subset* D₃
        ⊢A₂≡Π = subset* D₂
        ⊢A₄≡Π = subset* D₄
        ΠFG′≡ΠFG′₂ = whrDet* (D₂ , Πₙ) (D₂′ , Πₙ)
        ΠFG′≡ΠFG′₄ = whrDet* (D₄ , Πₙ) (D₄′ , Πₙ)
        ⊢A₁≡A₂ = escapeEq {l = ι ⁰} [A₁] (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A₃] [t≡t′]) ⊢A₃≡Π
        F′≡F′₄ , _ , _ , G′≡G′₄ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₄
        F′≡F′₂ , _ , _ , G′≡G′₂ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₂
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁))) (un-univ≡ ⊢A₃≡Π) (un-univ≡ ⊢A₁≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₄ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₄ ⊢A₄≡Π))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₂ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₂ ⊢A₂≡Π))))
        cast~cast = ~-conv (~-castΠΠ%! (un-univ ⊢F₃) (un-univ ⊢G₃) (≅-un-univ A₃≡A₄′) (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₂′) ⊢t≡t ⊢e' ⊢e′') (sym ⊢A₁≡Π)
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F₃ ^ % ° ⁰ ▹ G₃ ° ⁰ ° ⁰ ^ !) (Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ (Π F₄ ^ % ° ⁰ ▹ G₄ ° ⁰ ° ⁰ ^ !)  (Π F₂ ^ ! ° ⁰ ▹ G₂ ° ⁰ ° ⁰ ^ !) e′ t′}
                     [A₁]
                     castΠΠ%!ₙ castΠΠ%!ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A₁ ⊢e ⊢t (un-univ:⇒*: [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₃ ) (un-univ ⊢G₃) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁) )) (un-univ≡ ⊢A₃≡Π)
                                                                  (refl (un-univ ⊢A₁))))) (conv ⊢t ⊢A₃≡Π) [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A₂ ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₄ ) (un-univ ⊢G₄) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₂) )) (un-univ≡ ⊢A₄≡Π)
                                                                  (refl (un-univ ⊢A₂))))) (conv ⊢t′ ⊢A₄≡Π) [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]])) (sym (≅-eq ⊢A₁≡A₂)))
                      (~-irrelevanceTerm PE.refl PE.refl (PE.cong₄ (λ X Y X' Y' → cast ⁰ (Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π X' ^ ! ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₄) (PE.sym G′≡G′₄) (PE.sym F′≡F′₂) (PE.sym G′≡G′₂)) cast~cast))

[castextShape] {A₃} {A₄} {A₁} {A₂} {Γ} {r = !} ⊢Γ
  _ _
  (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′])
  _ _
  (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′]) =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [A₁] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        [A₃] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
        [A₄] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
        ⊢t = escapeTerm [A₃] [t]
        ⊢t′ = escapeTerm [A₄] [t′]
        ⊢A₁≡Π = subset* D₁
        ⊢A₃≡Π = subset* D₃
        ⊢A₂≡Π = subset* D₂
        ⊢A₄≡Π = subset* D₄
        ΠFG′≡ΠFG′₂ = whrDet* (D₂ , Πₙ) (D₂′ , Πₙ)
        ΠFG′≡ΠFG′₄ = whrDet* (D₄ , Πₙ) (D₄′ , Πₙ)
        ⊢A₁≡A₂ = escapeEq {l = ι ⁰} [A₁] (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A₃] [t≡t′]) ⊢A₃≡Π
        F′≡F′₄ , _ , _ , G′≡G′₄ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₄
        F′≡F′₂ , _ , _ , G′≡G′₂ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₂
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁))) (un-univ≡ ⊢A₃≡Π)(un-univ≡ ⊢A₁≡Π) ))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₄ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₄ ⊢A₄≡Π))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₂ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₂ ⊢A₂≡Π))))
        cast~cast = ~-conv (~-castΠΠ%! (un-univ ⊢F₃) (un-univ ⊢G₃) (≅-un-univ A₃≡A₄′) (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₂′) ⊢t≡t ⊢e' ⊢e′') (sym ⊢A₁≡Π)
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F₃ ^ % ° ⁰ ▹ G₃ ° ⁰ ° ⁰ ^ !) (Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ (Π F₄ ^ % ° ⁰ ▹ G₄ ° ⁰ ° ⁰ ^ !)  (Π F₂ ^ ! ° ⁰ ▹ G₂ ° ⁰ ° ⁰ ^ !) e′ t′}
                     [A₁]
                     castΠΠ%!ₙ castΠΠ%!ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A₁ ⊢e ⊢t (un-univ:⇒*: [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₃ ) (un-univ ⊢G₃) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁) )) (un-univ≡ ⊢A₃≡Π)
                                                                  (refl (un-univ ⊢A₁))))) (conv ⊢t ⊢A₃≡Π) [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A₂ ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₄ ) (un-univ ⊢G₄) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₂) )) (un-univ≡ ⊢A₄≡Π)
                                                                  (refl (un-univ ⊢A₂))))) (conv ⊢t′ ⊢A₄≡Π) [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]])) (sym (≅-eq ⊢A₁≡A₂)))
                      (~-irrelevanceTerm PE.refl PE.refl (PE.cong₄ (λ X Y X' Y' → cast ⁰ (Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π X' ^ ! ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₄) (PE.sym G′≡G′₄) (PE.sym F′≡F′₂) (PE.sym G′≡G′₂)) cast~cast)) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [A₁] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        [A₃] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
        [A₂] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
        ⊢t = escapeTerm [A₁] [t]
        ⊢t′ = escapeTerm [A₂] [t′]
        ⊢A₁≡Π = subset* D₁
        ⊢A₃≡Π = subset* D₃
        ⊢A₂≡Π = subset* D₂
        ⊢A₄≡Π = subset* D₄
        ⊢A₃≡A₄ = escapeEq {l = ι ⁰} [A₃] (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′])
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A₁] [t≡t′]) ⊢A₁≡Π
        ΠFG′≡ΠFG′₂ = whrDet* (D₂ , Πₙ) (D₂′ , Πₙ)
        F′≡F′₂ , _ , _ , G′≡G′₂ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₂
        ΠFG′≡ΠFG′₄ = whrDet* (D₄ , Πₙ) (D₄′ , Πₙ)
        F′≡F′₄ , _ , _ , G′≡G′₄ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₄
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁))) (un-univ≡ ⊢A₁≡Π) (un-univ≡ ⊢A₃≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₁)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₂ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₂ ⊢A₂≡Π))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ A₄ ≡ X ^ [ ! , ι ⁰ ]) ΠFG′≡ΠFG′₄ ⊢A₄≡Π))))
        cast~cast = ~-conv (~-castΠΠ!% (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₂′) (un-univ ⊢F₃) (un-univ ⊢G₃) (≅-un-univ A₃≡A₄′) ⊢t≡t ⊢e' ⊢e′') (sym ⊢A₃≡Π)
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ° ⁰ ^ !) (Π F₃ ^ % ° ⁰ ▹ G₃ ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ (Π F₂ ^ ! ° ⁰ ▹ G₂ ° ⁰ ° ⁰ ^ !)  (Π F₄ ^ % ° ⁰ ▹ G₄ ° ⁰ ° ⁰ ^ !) e′ t′}
                     [A₃]
                     castΠΠ!%ₙ castΠΠ!%ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A₃ ⊢e ⊢t (un-univ:⇒*: [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₁ ) (un-univ ⊢G₁) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A₃) )) (un-univ≡ ⊢A₁≡Π)
                                                                  (refl (un-univ ⊢A₃))))) (conv ⊢t ⊢A₁≡Π) [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A₄ ⊢e′ ⊢t′ (un-univ:⇒*: [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]]))
                                    (CastRed*TermΠ (un-univ ⊢F₂ ) (un-univ ⊢G₂) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A₄) )) (un-univ≡ ⊢A₂≡Π)
                                                                  (refl (un-univ ⊢A₄))))) (conv ⊢t′ ⊢A₂≡Π) [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]])) (sym (≅-eq ⊢A₃≡A₄)))
                      (~-irrelevanceTerm PE.refl PE.refl (PE.cong₄ (λ X Y X' Y' → cast ⁰ (Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π X' ^ % ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₂) (PE.sym G′≡G′₂) (PE.sym F′≡F′₄) (PE.sym G′≡G′₄)) cast~cast))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕᵣ ℕA₁) .(ℕᵣ ℕB₁) (ℕᵥ ℕA₁ ℕB₁) [A≡C] .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ → [castext]ℕ ⊢Γ ℕA₁ ℕB₁ [A≡C] ℕA ℕB [B≡D] (escapeTerm {l = ι ⁰} (ℕᵣ ℕA₁) [t]) (escapeTerm {l = ι ⁰} (ℕᵣ ℕB₁) [t′]) [t≡t′] ⊢e ⊢e′ ) ,
  λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ → [castext]ℕ ⊢Γ ℕA ℕB [B≡D] ℕA₁ ℕB₁ [A≡C]  (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) [t≡t′] ⊢e ⊢e′

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕ2ᵣ ℕ2A₁) .(ℕ2ᵣ ℕ2B₁) (ℕ2ᵥ ℕ2A₁ ℕ2B₁) [A≡C] .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ → [castext]ℕ2 ⊢Γ ℕ2A₁ ℕ2B₁ [A≡C] ℕ2A ℕ2B [B≡D] (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A₁) [t]) (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B₁) [t′]) [t≡t′] ⊢e ⊢e′ ) ,
  λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ → [castext]ℕ2 ⊢Γ ℕ2A ℕ2B [B≡D] ℕ2A₁ ℕ2B₁ [A≡C]  (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) [t≡t′] ⊢e ⊢e′

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕᵣ ℕA₁) .(ℕᵣ ℕB₁) (ℕᵥ ℕA₁ ℕB₁) [A≡C] .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    [castext]ℕℕ2 ⊢Γ ℕA₁ ℕB₁ [A≡C] ℕ2A ℕ2B [B≡D] [t] [t′] [t≡t′] ⊢e ⊢e′) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    [castext]ℕ2ℕ ⊢Γ ℕ2A ℕ2B [B≡D] ℕA₁ ℕB₁ [A≡C] [t] [t′] [t≡t′] ⊢e ⊢e′)

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕ2ᵣ ℕ2A₁) .(ℕ2ᵣ ℕ2B₁) (ℕ2ᵥ ℕ2A₁ ℕ2B₁) [A≡C] .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    [castext]ℕ2ℕ ⊢Γ ℕ2A₁ ℕ2B₁ [A≡C] ℕA ℕB [B≡D] [t] [t′] [t≡t′] ⊢e ⊢e′) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    [castext]ℕℕ2 ⊢Γ ℕA ℕB [B≡D] ℕ2A₁ ℕ2B₁ [A≡C] [t] [t′] [t≡t′] ⊢e ⊢e′)

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ne neA) .(ne neB) (ne neA neB) [A≡C] .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [B≡D] =
  ([castext]Ne ⊢Γ neA neB [A≡C] (ℕ2ᵣ ℕ2A) (ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [B≡D]) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [A≡C]
        ⊢B≡ℕ2 = subset* (red ℕ2A)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) ⊢B≡ℕ2
        ⊢D≡ℕ2 = subset* (red ℕ2B)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) ⊢D≡ℕ2
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t≡t′]
        ⊢A≡K = subset* D
        ⊢C≡K = subset* D′
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡ℕ2) (un-univ≡ ⊢A≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢D≡ℕ2) (un-univ≡ ⊢C≡K)))
    in neₜ₌ (cast ⁰ ℕ2 K e t) (cast ⁰ ℕ2 K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) (un-univ:⇒*: ℕ2A))
                                                   (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ2)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) (un-univ:⇒*: ℕ2B))
                                                   (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′) )) (un-univ≡ ⊢D≡ℕ2)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castℕ2ₙ neK) (castℕ2ₙ neK') (~-castℕ2 ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡ℕ2) ⊢e' ⊢e′')))

[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        [[ _ , _ , DB ]] = ℕ2A
        ⊢B≡ℕ2 = subset* DB
        [[ _ , _ , DD ]] = ℕ2B
        ⊢D≡ℕ2 = subset* DD
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕ2ᵣ ℕ2A)
        ⊢D = escape {l = ι ⁰} (ℕ2ᵣ ℕ2B)
        ⊢B≡D = escapeEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡ℕ2)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ C ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡ℕ2)))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castΠℕ2 (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ℕ2 e t} {n′ = cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) ℕ2 e′ t′} (ℕ2ᵣ ℕ2A)
                     castΠℕ2ₙ castΠℕ2ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t ℕ2A))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ ℕ2B)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* (red ℕ2A))))),
  λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A≡Π = subset* DΠA
        ⊢B≡ℕ2 = subset* (red ℕ2A)
        ⊢D≡ℕ2 = subset* (red ℕ2B)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) ⊢B≡ℕ2
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) ⊢D≡ℕ2
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕ2ᵣ ℕ2A)
        ⊢D = escape {l = ι ⁰} (ℕ2ᵣ ℕ2B)
        ⊢A≡C = escapeEq {l = ι ⁰} (Πᵣ ΠA) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡ℕ2) (un-univ≡ ⊢A≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ ⊢D≡ℕ2)
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ C ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ _ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castℕ2Π (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢B≡ℕ2) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: { n = cast ⁰ ℕ2 (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ ℕ2  (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) e′ t′} (Πᵣ ΠA)
                     castℕ2Πₙ castℕ2Πₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) (un-univ:⇒*: ℕ2A))
                                      (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ2)
                                                                  (refl (un-univ ⊢A)))))
                                                     ⊢t [[ ⊢A , ⊢Π , DΠA ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) (un-univ:⇒*: ℕ2B))
                                     (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢D≡ℕ2)
                                                                  (refl (un-univ ⊢C))))) ⊢t′ [[ ⊢C , ⊢Π′ , DΠB ]])) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DΠA)))

[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [A≡C]
                                              _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢D , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢D′ , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢D , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A≡Π = subset* DΠA
        ⊢B≡ℕ2 = subset* (red ℕ2A)
        ⊢D≡ℕ2 = subset* (red ℕ2B)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) ⊢B≡ℕ2
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) ⊢D≡ℕ2
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢A≡C = escapeEq {l = ι ⁰} (Πᵣ ΠA) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D))) (un-univ≡ ⊢B≡ℕ2) (un-univ≡ ⊢A≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D)))
                        (un-univ≡ ⊢D≡ℕ2)
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ D ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ _ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castℕ2Π (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢B≡ℕ2) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ ℕ2 (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ ℕ2  (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) e′ t′} (Πᵣ ΠA)
                     castℕ2Πₙ castℕ2Πₙ
                     (transTerm:⇒:* (CastRed*Term ⊢D ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) (un-univ:⇒*: ℕ2A))
                                      (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D) )) (un-univ≡ ⊢B≡ℕ2)
                                                                  (refl (un-univ ⊢D))))) ⊢t [[ ⊢D , ⊢Π , DΠA ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D′ ⊢e′ (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) (un-univ:⇒*: ℕ2B))
                                     (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D′) )) (un-univ≡ ⊢D≡ℕ2)
                                                                  (refl (un-univ ⊢D′))))) ⊢t′ [[ ⊢D′ , ⊢Π′ , DΠB ]])) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DΠA)))) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢D , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢D′ , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕ2ᵣ ℕ2A)
        ⊢Dnat = escape {l = ι ⁰} (ℕ2ᵣ ℕ2B)
        ⊢B≡ℕ2 = subset* (red ℕ2A)
        ⊢D≡ℕ2 = subset* (red ℕ2B)
        ⊢B≡D = escapeEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [A≡C]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡ℕ2)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ D ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡ℕ2)))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castΠℕ2 (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ℕ2 e t} {n′ = cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) ℕ2 e′ t′} (ℕ2ᵣ ℕ2A)
                     castΠℕ2ₙ castΠℕ2ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢D , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t ℕ2A))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢Dnat ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢D′ , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D′) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢Dnat))))) ⊢t′ ℕ2B)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* (red ℕ2A)))))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ne neA) .(ne neB) (ne neA neB) [A≡C] .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  ([castext]Ne ⊢Γ neA neB [A≡C] (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D]) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [A≡C]
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) ⊢B≡ℕ
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) ⊢D≡ℕ
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
        ⊢A≡K = subset* D
        ⊢C≡K = subset* D′
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡ℕ) (un-univ≡ ⊢A≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢D≡ℕ) (un-univ≡ ⊢C≡K)))
    in neₜ₌ (cast ⁰ ℕ K e t) (cast ⁰ ℕ K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                                   (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′) )) (un-univ≡ ⊢D≡ℕ)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castℕₙ neK) (castℕₙ neK') (~-castℕ ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡ℕ) ⊢e' ⊢e′')))
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        [[ _ , _ , DB ]] = ℕA
        ⊢B≡ℕ = subset* DB
        [[ _ , _ , DD ]] = ℕB
        ⊢D≡ℕ = subset* DD
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕᵣ ℕA)
        ⊢D = escape {l = ι ⁰} (ℕᵣ ℕB)
        ⊢B≡D = escapeEq {l = ι ⁰} (ℕᵣ ℕA) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡ℕ)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ C ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡ℕ)))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castΠℕ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ℕ e t} {n′ = cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) ℕ e′ t′} (ℕᵣ ℕA)
                     castΠℕₙ castΠℕₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t ℕA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ ℕB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* (red ℕA))))),
  λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A≡Π = subset* DΠA
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) ⊢B≡ℕ
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) ⊢D≡ℕ
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕᵣ ℕA)
        ⊢D = escape {l = ι ⁰} (ℕᵣ ℕB)
        ⊢A≡C = escapeEq {l = ι ⁰} (Πᵣ ΠA) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡ℕ) (un-univ≡ ⊢A≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ ⊢D≡ℕ)
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ C ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ _ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castℕΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢B≡ℕ) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: { n = cast ⁰ ℕ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ ℕ  (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) e′ t′} (Πᵣ ΠA)
                     castℕΠₙ castℕΠₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                      (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ)
                                                                  (refl (un-univ ⊢A)))))
                                                     ⊢t [[ ⊢A , ⊢Π , DΠA ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                     (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢D≡ℕ)
                                                                  (refl (un-univ ⊢C))))) ⊢t′ [[ ⊢C , ⊢Π′ , DΠB ]])) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DΠA)))
[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [A≡C] .(ne neA) .(ne neB) (ne neA neB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [B≡D]
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢A≡K = subset* D
        ⊢C≡K = subset* D′
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) ⊢B≡ℕ
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) ⊢D≡ℕ
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡ℕ) (un-univ≡ ⊢A≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢D≡ℕ) (un-univ≡ ⊢C≡K)))
    in neₜ₌ (cast ⁰ ℕ K e t) (cast ⁰ ℕ K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                                   (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′) )) (un-univ≡ ⊢D≡ℕ)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castℕₙ neK) (castℕₙ neK') (~-castℕ ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡ℕ) ⊢e' ⊢e′'))) ,
  ([castext]Ne ⊢Γ neA neB [B≡D] (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [A≡C])

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [A≡C] .(ne neA) .(ne neB) (ne neA neB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [B≡D]
        ⊢B≡ℕ2 = subset* (red ℕ2A)
        ⊢A≡K = subset* D
        ⊢C≡K = subset* D′
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) ⊢B≡ℕ2
        ⊢D≡ℕ2 = subset* (red ℕ2B)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) ⊢D≡ℕ2
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t≡t′]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡ℕ2) (un-univ≡ ⊢A≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢D≡ℕ2) (un-univ≡ ⊢C≡K)))
    in neₜ₌ (cast ⁰ ℕ2 K e t) (cast ⁰ ℕ2 K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) (un-univ:⇒*: ℕ2A))
                                                   (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ2)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) (un-univ:⇒*: ℕ2B))
                                                   (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′) )) (un-univ≡ ⊢D≡ℕ2)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castℕ2ₙ neK) (castℕ2ₙ neK') (~-castℕ2 ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡ℕ2) ⊢e' ⊢e′'))) ,
  ([castext]Ne ⊢Γ neA neB [B≡D] (ℕ2ᵣ ℕ2A) (ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [A≡C])
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(ne neA₁) .(ne neB₁) (ne neA₁ neB₁) [A≡C] .(ne neA) .(ne neB) (ne neA neB) [B≡D] =
  ([castext]Ne ⊢Γ neA₁ neB₁ [A≡C] (ne neA) (ne neB) (ne neA neB) [B≡D]) , ([castext]Ne ⊢Γ neA neB [B≡D] (ne neA₁) (ne neB₁) (ne neA₁ neB₁) [A≡C])
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) .(ne neA) .(ne neB) (ne neA neB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢B , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢D , ⊢K′ , D′ ]] neK' K≡K' = [B≡D]
        ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        ⊢B≡K = subset* D
        ⊢D≡K = subset* D′
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        ⊢B≡D = escapeEq {l = ι ⁰} (ne neA) [B≡D]
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ C ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡K)))
    in neuEqTerm:⇒*: {l = ι ⁰} {n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) K e t} {n′ =  cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) K′ e′ t′}
                     (ne neA) (castΠₙ neK) (castΠₙ neK')
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ [[ ⊢D , ⊢K′ , D′ ]]))
                      (sym (≅-eq ⊢B≡D)))
                      (~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                        (~-conv (~-castΠ (≅-un-univ A≡B) K≡K' (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′') (sym (subset* D))))) ,
  ([castext]Ne ⊢Γ neA neB [B≡D] (Πᵣ′ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                (Πᵣ′ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′)
                                (Πᵥ (Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]))

[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D]
                                              _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A≡Π = subset* DΠA
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) ⊢B≡ℕ
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) ⊢D≡ℕ
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕᵣ ℕA)
        ⊢D = escape {l = ι ⁰} (ℕᵣ ℕB)
        ⊢A≡C = escapeEq {l = ι ⁰} (Πᵣ ΠA) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡ℕ) (un-univ≡ ⊢A≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ ⊢D≡ℕ)
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ D ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))))

        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ _ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castℕΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢B≡ℕ) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ ℕ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ ℕ  (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) e′ t′} (Πᵣ ΠA)
                     castℕΠₙ castℕΠₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                      (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ)
                                                                  (refl (un-univ ⊢A)))))
                                                     ⊢t [[ ⊢A , ⊢Π , DΠA ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                     (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢D≡ℕ)
                                                                  (refl (un-univ ⊢C))))) ⊢t′ [[ ⊢C , ⊢Π′ , DΠB ]])) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DΠA)))) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕᵣ ℕA)
        ⊢D = escape {l = ι ⁰} (ℕᵣ ℕB)
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢B≡D = escapeEq {l = ι ⁰} (ℕᵣ ℕA) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡ℕ)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ D ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡ℕ)))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castΠℕ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ℕ e t} {n′ = cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) ℕ e′ t′} (ℕᵣ ℕA)
                     castΠℕₙ castΠℕₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t ℕA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ ℕB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* (red ℕA)))))

[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(ne neA) .(ne neB) (ne neA neB) [B≡D]
                                              _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) =
  ([castext]Ne ⊢Γ neA neB [B≡D] (Πᵣ′ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                (Πᵣ′ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′)
                                (Πᵥ (Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢B , ⊢K , DB ]] neK K≡K = neA
        ne₌ K′ [[ ⊢D , ⊢K′ , D′ ]] neK' K≡K' = [B≡D]
        ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        ⊢B≡K = subset* DB
        ⊢D≡K = subset* D′
        ⊢B≡D = escapeEq {l = ι ⁰} (ne neA) [B≡D]
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ D ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡K)))

    in neuEqTerm:⇒*: {l = ι ⁰} {n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) K e t} {n′ =  cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) K′ e′ t′}
                     (ne neA) (castΠₙ neK) (castΠₙ neK')
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , DB ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ [[ ⊢D , ⊢K′ , D′ ]]))
                      (sym (≅-eq ⊢B≡D)))
                      (~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                        (~-conv (~-castΠ (≅-un-univ A≡B) K≡K' (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′') (sym (subset* DB)))))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(Indᵣ IndA₁) .(Indᵣ IndB₁) (Indᵥ {i = i} IndA₁ IndB₁) [A≡C] .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ {i = i′} IndA IndB) [B≡D] = go (i ≟ i′)
  where
    go : Nullary.Dec (i PE.≡ i′) → _
    go (Nullary.yes PE.refl) =
      (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ → [castext]Ind ⊢Γ IndA₁ IndB₁ [A≡C] IndA IndB [B≡D] (escapeTerm {l = ι ⁰} (Indᵣ IndA₁) [t]) (escapeTerm {l = ι ⁰} (Indᵣ IndB₁) [t′]) [t≡t′] ⊢e ⊢e′ ) ,
      λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ → [castext]Ind ⊢Γ IndA IndB [B≡D] IndA₁ IndB₁ [A≡C]  (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) [t≡t′] ⊢e ⊢e′
    go (Nullary.no i≢i′) =
      (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
        let [[ ⊢A , ⊢IA , DA ]] = IndA₁
            [[ ⊢C , ⊢IC , DC ]] = IndB₁
            [[ ⊢B , ⊢IB , DB ]] = IndA
            [[ ⊢D , ⊢ID , DD ]] = IndB
            ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA₁) [t]) (subset* DA)
            ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB₁) [t′]) (subset* DC)
            t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA₁) [t≡t′]
            ⊢B≡D = escapeEq {l = ι ⁰} (Indᵣ IndA) [B≡D]
            ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
            ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DC)) (un-univ≡ (subset* DD))))
            cast~cast = ~-castIndInd≢ i≢i′ (≅-conv t≅t′ (subset* DA)) ⊢e' ⊢e′'
        in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ IndA) (castIndInd≢ₙ i≢i′) (castIndInd≢ₙ i≢i′)
                         (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA₁) [t]) (un-univ:⇒*: IndA₁))
                                          (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA))
                                                                      (refl (un-univ ⊢B))))) ⊢t IndA))
                         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB₁) [t′]) (un-univ:⇒*: IndB₁))
                                         (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DC))
                                                                      (refl (un-univ ⊢D))))) ⊢t′ IndB)) (sym (≅-eq ⊢B≡D)))
                         (~-conv cast~cast (sym (subset* DB)))) ,
      (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
        let i′≢i : i′ PE.≢ i
            i′≢i eq = i≢i′ (PE.sym eq)
            [[ ⊢A , ⊢IA , DA ]] = IndA₁
            [[ ⊢C , ⊢IC , DC ]] = IndB₁
            [[ ⊢B , ⊢IB , DB ]] = IndA
            [[ ⊢D , ⊢ID , DD ]] = IndB
            ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (subset* DB)
            ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (subset* DD)
            t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA) [t≡t′]
            ⊢A≡C = escapeEq {l = ι ⁰} (Indᵣ IndA₁) [A≡C]
            ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (un-univ≡ (subset* DA))))
            ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DD)) (un-univ≡ (subset* DC))))
            cast~cast = ~-castIndInd≢ i′≢i (≅-conv t≅t′ (subset* DB)) ⊢e' ⊢e′'
        in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ IndA₁) (castIndInd≢ₙ i′≢i) (castIndInd≢ₙ i′≢i)
                         (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (un-univ:⇒*: IndA))
                                          (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB))
                                                                      (refl (un-univ ⊢A))))) ⊢t IndA₁))
                         (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (un-univ:⇒*: IndB))
                                         (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DD))
                                                                      (refl (un-univ ⊢C))))) ⊢t′ IndB₁)) (sym (≅-eq ⊢A≡C)))
                         (~-conv cast~cast (sym (subset* DA))))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(Indᵣ IndA₁) .(Indᵣ IndB₁) (Indᵥ IndA₁ IndB₁) [A≡C] .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢IA , DA ]] = IndA₁
        [[ ⊢C , ⊢IC , DC ]] = IndB₁
        [[ ⊢B , ⊢ℕB , DB ]] = ℕA
        [[ ⊢D , ⊢ℕD , DD ]] = ℕB
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA₁) [t]) (subset* DA)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB₁) [t′]) (subset* DC)
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA₁) [t≡t′]
        ⊢B≡D = escapeEq {l = ι ⁰} (ℕᵣ ℕA) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DC)) (un-univ≡ (subset* DD))))
        cast~cast = ~-castIndℕ (≅-conv t≅t′ (subset* DA)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (ℕᵣ ℕA) castIndℕₙ castIndℕₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA₁) [t]) (un-univ:⇒*: IndA₁))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) ⊢t ℕA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB₁) [t′]) (un-univ:⇒*: IndB₁))
                                     (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DC))
                                                                  (refl (un-univ ⊢D))))) ⊢t′ ℕB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* DB)))) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢IA , DA ]] = IndA₁
        [[ ⊢C , ⊢IC , DC ]] = IndB₁
        [[ ⊢B , ⊢ℕB , DB ]] = ℕA
        [[ ⊢D , ⊢ℕD , DD ]] = ℕB
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (subset* DB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (subset* DD)
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
        ⊢A≡C = escapeEq {l = ι ⁰} (Indᵣ IndA₁) [A≡C]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (un-univ≡ (subset* DA))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DD)) (un-univ≡ (subset* DC))))
        cast~cast = ~-castℕInd (≅-conv t≅t′ (subset* DB)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ IndA₁) castℕIndₙ castℕIndₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                      (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB))
                                                                  (refl (un-univ ⊢A))))) ⊢t IndA₁))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                     (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DD))
                                                                  (refl (un-univ ⊢C))))) ⊢t′ IndB₁)) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DA))))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕᵣ ℕA₁) .(ℕᵣ ℕB₁) (ℕᵥ ℕA₁ ℕB₁) [A≡C] .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ IndA IndB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢ℕA , DA ]] = ℕA₁
        [[ ⊢C , ⊢ℕC , DC ]] = ℕB₁
        [[ ⊢B , ⊢IB , DB ]] = IndA
        [[ ⊢D , ⊢ID , DD ]] = IndB
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA₁) [t]) (subset* DA)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB₁) [t′]) (subset* DC)
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA₁) [t≡t′]
        ⊢B≡D = escapeEq {l = ι ⁰} (Indᵣ IndA) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DC)) (un-univ≡ (subset* DD))))
        cast~cast = ~-castℕInd (≅-conv t≅t′ (subset* DA)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ IndA) castℕIndₙ castℕIndₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA₁) [t]) (un-univ:⇒*: ℕA₁))
                                      (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) ⊢t IndA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB₁) [t′]) (un-univ:⇒*: ℕB₁))
                                     (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DC))
                                                                  (refl (un-univ ⊢D))))) ⊢t′ IndB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* DB)))) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢ℕA , DA ]] = ℕA₁
        [[ ⊢C , ⊢ℕC , DC ]] = ℕB₁
        [[ ⊢B , ⊢IB , DB ]] = IndA
        [[ ⊢D , ⊢ID , DD ]] = IndB
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (subset* DB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (subset* DD)
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA) [t≡t′]
        ⊢A≡C = escapeEq {l = ι ⁰} (ℕᵣ ℕA₁) [A≡C]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (un-univ≡ (subset* DA))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DD)) (un-univ≡ (subset* DC))))
        cast~cast = ~-castIndℕ (≅-conv t≅t′ (subset* DB)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (ℕᵣ ℕA₁) castIndℕₙ castIndℕₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (un-univ:⇒*: IndA))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB))
                                                                  (refl (un-univ ⊢A))))) ⊢t ℕA₁))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (un-univ:⇒*: IndB))
                                     (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DD))
                                                                  (refl (un-univ ⊢C))))) ⊢t′ ℕB₁)) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DA))))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(Indᵣ IndA₁) .(Indᵣ IndB₁) (Indᵥ IndA₁ IndB₁) [A≡C] .(ℕ2ᵣ ℕ2A) .(ℕ2ᵣ ℕ2B) (ℕ2ᵥ ℕ2A ℕ2B) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢IA , DA ]] = IndA₁
        [[ ⊢C , ⊢IC , DC ]] = IndB₁
        [[ ⊢B , ⊢ℕ2B , DB ]] = ℕ2A
        [[ ⊢D , ⊢ℕ2D , DD ]] = ℕ2B
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA₁) [t]) (subset* DA)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB₁) [t′]) (subset* DC)
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA₁) [t≡t′]
        ⊢B≡D = escapeEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DC)) (un-univ≡ (subset* DD))))
        cast~cast = ~-castIndℕ2 (≅-conv t≅t′ (subset* DA)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (ℕ2ᵣ ℕ2A) castIndℕ2ₙ castIndℕ2ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA₁) [t]) (un-univ:⇒*: IndA₁))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) ⊢t ℕ2A))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB₁) [t′]) (un-univ:⇒*: IndB₁))
                                     (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DC))
                                                                  (refl (un-univ ⊢D))))) ⊢t′ ℕ2B)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* DB)))) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢IA , DA ]] = IndA₁
        [[ ⊢C , ⊢IC , DC ]] = IndB₁
        [[ ⊢B , ⊢ℕ2B , DB ]] = ℕ2A
        [[ ⊢D , ⊢ℕ2D , DD ]] = ℕ2B
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) (subset* DB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) (subset* DD)
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t≡t′]
        ⊢A≡C = escapeEq {l = ι ⁰} (Indᵣ IndA₁) [A≡C]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (un-univ≡ (subset* DA))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DD)) (un-univ≡ (subset* DC))))
        cast~cast = ~-castℕ2Ind (≅-conv t≅t′ (subset* DB)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ IndA₁) castℕ2Indₙ castℕ2Indₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A) [t]) (un-univ:⇒*: ℕ2A))
                                      (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB))
                                                                  (refl (un-univ ⊢A))))) ⊢t IndA₁))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B) [t′]) (un-univ:⇒*: ℕ2B))
                                     (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DD))
                                                                  (refl (un-univ ⊢C))))) ⊢t′ IndB₁)) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DA))))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕ2ᵣ ℕ2A₁) .(ℕ2ᵣ ℕ2B₁) (ℕ2ᵥ ℕ2A₁ ℕ2B₁) [A≡C] .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ IndA IndB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢ℕ2A , DA ]] = ℕ2A₁
        [[ ⊢C , ⊢ℕ2C , DC ]] = ℕ2B₁
        [[ ⊢B , ⊢IB , DB ]] = IndA
        [[ ⊢D , ⊢ID , DD ]] = IndB
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A₁) [t]) (subset* DA)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B₁) [t′]) (subset* DC)
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕ2ᵣ ℕ2A₁) [t≡t′]
        ⊢B≡D = escapeEq {l = ι ⁰} (Indᵣ IndA) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DC)) (un-univ≡ (subset* DD))))
        cast~cast = ~-castℕ2Ind (≅-conv t≅t′ (subset* DA)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (Indᵣ IndA) castℕ2Indₙ castℕ2Indₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2A₁) [t]) (un-univ:⇒*: ℕ2A₁))
                                      (CastRed*Termℕ2 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) ⊢t IndA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (ℕ2ᵣ ℕ2B₁) [t′]) (un-univ:⇒*: ℕ2B₁))
                                     (CastRed*Termℕ2 (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DC))
                                                                  (refl (un-univ ⊢D))))) ⊢t′ IndB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* DB)))) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let [[ ⊢A , ⊢ℕ2A , DA ]] = ℕ2A₁
        [[ ⊢C , ⊢ℕ2C , DC ]] = ℕ2B₁
        [[ ⊢B , ⊢IB , DB ]] = IndA
        [[ ⊢D , ⊢ID , DD ]] = IndB
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (subset* DB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (subset* DD)
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA) [t≡t′]
        ⊢A≡C = escapeEq {l = ι ⁰} (ℕ2ᵣ ℕ2A₁) [A≡C]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB)) (un-univ≡ (subset* DA))))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DD)) (un-univ≡ (subset* DC))))
        cast~cast = ~-castIndℕ2 (≅-conv t≅t′ (subset* DB)) ⊢e' ⊢e′'
    in neuEqTerm:⇒*: {l = ι ⁰} (ℕ2ᵣ ℕ2A₁) castIndℕ2ₙ castIndℕ2ₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (un-univ:⇒*: IndA))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ (subset* DB))
                                                                  (refl (un-univ ⊢A))))) ⊢t ℕ2A₁))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (un-univ:⇒*: IndB))
                                     (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ (subset* DD))
                                                                  (refl (un-univ ⊢C))))) ⊢t′ ℕ2B₁)) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DA))))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ne neA) .(ne neB) (ne neA neB) [A≡C] .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ IndA IndB) [B≡D] =
  ([castext]Ne ⊢Γ neA neB [A≡C] (Indᵣ IndA) (Indᵣ IndB) (Indᵥ IndA IndB) [B≡D]) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [A≡C]
        ⊢B≡I = subset* (red IndA)
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) ⊢B≡I
        ⊢D≡I = subset* (red IndB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) ⊢D≡I
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA) [t≡t′]
        ⊢A≡K = subset* D
        ⊢C≡K = subset* D′
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡I) (un-univ≡ ⊢A≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢D≡I) (un-univ≡ ⊢C≡K)))
    in neₜ₌ (cast ⁰ (Ind _) K e t) (cast ⁰ (Ind _) K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (un-univ:⇒*: IndA))
                                                   (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡I)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (un-univ:⇒*: IndB))
                                                   (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′))) (un-univ≡ ⊢D≡I)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castIndₙ neK) (castIndₙ neK') (~-castInd ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡I) ⊢e' ⊢e′')))

[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ IndA IndB) [A≡C] .(ne neA) .(ne neB) (ne neA neB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [B≡D]
        ⊢B≡I = subset* (red IndA)
        ⊢A≡K = subset* D
        ⊢C≡K = subset* D′
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) ⊢B≡I
        ⊢D≡I = subset* (red IndB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) ⊢D≡I
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA) [t≡t′]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡I) (un-univ≡ ⊢A≡K)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢D≡I) (un-univ≡ ⊢C≡K)))
    in neₜ₌ (cast ⁰ (Ind _) K e t) (cast ⁰ (Ind _) K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (un-univ:⇒*: IndA))
                                                   (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡I)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (un-univ:⇒*: IndB))
                                                   (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′))) (un-univ≡ ⊢D≡I)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castIndₙ neK) (castIndₙ neK') (~-castInd ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡I) ⊢e' ⊢e′'))) ,
  ([castext]Ne ⊢Γ neA neB [B≡D] (Indᵣ IndA) (Indᵣ IndB) (Indᵥ IndA IndB) [A≡C])

[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ IndA IndB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        [[ _ , _ , DB ]] = IndA
        ⊢B≡I = subset* DB
        [[ _ , _ , DD ]] = IndB
        ⊢D≡I = subset* DD
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (Indᵣ IndA)
        ⊢D = escape {l = ι ⁰} (Indᵣ IndB)
        ⊢B≡D = escapeEq {l = ι ⁰} (Indᵣ IndA) [B≡D]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡I)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ C ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡I)))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castΠInd (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) (Ind _) e t} {n′ = cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) (Ind _) e′ t′} (Indᵣ IndA)
                     castΠIndₙ castΠIndₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t IndA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ IndB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* (red IndA))))),
  λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A≡Π = subset* DΠA
        ⊢B≡I = subset* (red IndA)
        ⊢D≡I = subset* (red IndB)
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) ⊢B≡I
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) ⊢D≡I
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢A≡C = escapeEq {l = ι ⁰} (Πᵣ ΠA) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡I) (un-univ≡ ⊢A≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A)))
                        (un-univ≡ ⊢D≡I)
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ C ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ _ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castIndΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢B≡I) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: { n = cast ⁰ (Ind _) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ (Ind _)  (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) e′ t′} (Πᵣ ΠA)
                     castIndΠₙ castIndΠₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (un-univ:⇒*: IndA))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢B≡I)
                                                                  (refl (un-univ ⊢A)))))
                                                     ⊢t [[ ⊢A , ⊢Π , DΠA ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (un-univ:⇒*: IndB))
                                     (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C))) (un-univ≡ ⊢D≡I)
                                                                  (refl (un-univ ⊢C))))) ⊢t′ [[ ⊢C , ⊢Π′ , DΠB ]])) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DΠA)))

[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(Indᵣ IndA) .(Indᵣ IndB) (Indᵥ IndA IndB) [A≡C]
                                              _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢D , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢D′ , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢D , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A≡Π = subset* DΠA
        ⊢B≡I = subset* (red IndA)
        ⊢D≡I = subset* (red IndB)
        ⊢t = conv (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) ⊢B≡I
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) ⊢D≡I
        t≅t′ = escapeTermEq {l = ι ⁰} (Indᵣ IndA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢A≡C = escapeEq {l = ι ⁰} (Πᵣ ΠA) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D))) (un-univ≡ ⊢B≡I) (un-univ≡ ⊢A≡Π)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D)))
                        (un-univ≡ ⊢D≡I)
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ D ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ _ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castIndΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢B≡I) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Ind _) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) e t} {n′ = cast ⁰ (Ind _)  (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) e′ t′} (Πᵣ ΠA)
                     castIndΠₙ castIndΠₙ
                     (transTerm:⇒:* (CastRed*Term ⊢D ⊢e (escapeTerm {l = ι ⁰} (Indᵣ IndA) [t]) (un-univ:⇒*: IndA))
                                      (CastRed*TermInd (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D))) (un-univ≡ ⊢B≡I)
                                                                  (refl (un-univ ⊢D))))) ⊢t [[ ⊢D , ⊢Π , DΠA ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D′ ⊢e′ (escapeTerm {l = ι ⁰} (Indᵣ IndB) [t′]) (un-univ:⇒*: IndB))
                                     (CastRed*TermInd (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D′))) (un-univ≡ ⊢D≡I)
                                                                  (refl (un-univ ⊢D′))))) ⊢t′ [[ ⊢D′ , ⊢Π′ , DΠB ]])) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DΠA)))) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢D , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢D′ , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (Indᵣ IndA)
        ⊢Dnat = escape {l = ι ⁰} (Indᵣ IndB)
        ⊢B≡I = subset* (red IndA)
        ⊢D≡I = subset* (red IndB)
        ⊢B≡D = escapeEq {l = ι ⁰} (Indᵣ IndA) [A≡C]
        ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D))) (un-univ≡ ⊢A≡Π) (un-univ≡ ⊢B≡I)))
        ⊢e′' = conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D)))
                        (un-univ≡ (PE.subst (λ X → Γ ⊢ D ≡ X ^ [ ! , ι ⁰ ])
                                            (PE.cong₃ (λ X Y Z → Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) F′≡F′₁ rF≡rF′ G′≡G′₁) ⊢C≡Π))
                        (un-univ≡ ⊢D≡I)))
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰ ° ⁰ ^ !) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castΠInd (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢A≡Π) ⊢e' ⊢e′')
    in neuEqTerm:⇒*: {l = ι ⁰} { n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) (Ind _) e t} {n′ = cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰ ° ⁰ ^ !) (Ind _) e′ t′} (Indᵣ IndA)
                     castΠIndₙ castΠIndₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢D , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢D))) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t IndA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢Dnat ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢D′ , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢D′))) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢Dnat))))) ⊢t′ IndB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* (red IndA)))))


[castextShape] {A} {C} {B} {D} {Γ} {r = %} ⊢Γ [A] [C] _ [A≡C] [B] [D] _ [B≡D] =
  [castext]irr {A} {C} {B} {D} {Γ} ⊢Γ [A] [C] [A≡C] [B] [D] [B≡D] , [castext]irr {B} {D} {A} {C} {Γ} ⊢Γ [B] [D] [B≡D] [A] [C] [A≡C]


[castext] {A} {C} {B} {D} {Γ} ⊢Γ [A] [C] [A≡C] [B] [D] [B≡D] = [castextShape] ⊢Γ [A] [C] (goodCases [A] [C] [A≡C]) [A≡C] [B] [D] (goodCases [B] [D] [B≡D]) [B≡D]




cast∞ : ∀ {A B r t e Γ}
         (⊢Γ : ⊢ Γ)
         ([U] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([AU] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([BU] : Γ ⊩⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([A] : Γ ⊩⟨ ∞ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ∞ ⟩ B ^ [ r , ι ⁰ ])
         ([t] : Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         ([Id] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]) →
         ([e] : Γ ⊩⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Id] ) →
         Γ ⊩⟨ ∞ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B]
cast∞ {A} {B} {r} {t} {e} {Γ} ⊢Γ [U] [AU] [BU] [A] [B] [t] [Id] [e] =
  let
    [A]′ : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ]
    [A]′ = univEq [U] [AU]
    [B]′ : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ]
    [B]′ = univEq [U] [BU]
    [t]′ : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t]′ = irrelevanceTerm [A] (emb ∞< (emb emb< [A]′)) [t]
    ⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]
    ⊢e = escapeTerm [Id] [e]
    x : Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B]′
    x = proj₁ ([cast] ⊢Γ [A]′ [B]′) [t]′ ⊢e
  in irrelevanceTerm (emb ∞< (emb emb< [B]′)) [B] x


castext∞ : ∀ {A A' B B' r t t' e e' Γ}
         (⊢Γ : ⊢ Γ)
         ([U] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([U'] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([AU] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([AU'] : Γ ⊩⟨ ∞ ⟩ A' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([BU] : Γ ⊩⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U'])
         ([BU'] : Γ ⊩⟨ ∞ ⟩ B' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U'])
         ([UA≡UA'] : Γ ⊩⟨ ∞ ⟩ A ≡ A' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([UB≡UB'] : Γ ⊩⟨ ∞ ⟩ B ≡ B' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U'])
         ([A] : Γ ⊩⟨ ∞ ⟩ A ^ [ r , ι ⁰ ])
         ([A'] : Γ ⊩⟨ ∞ ⟩ A' ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ∞ ⟩ B ^ [ r , ι ⁰ ])
         ([B'] : Γ ⊩⟨ ∞ ⟩ B' ^ [ r , ι ⁰ ])
         ([t] : Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         ([t'] : Γ ⊩⟨ ∞ ⟩ t' ∷ A' ^ [ r , ι ⁰ ] / [A'])
         ([t≡t'] : Γ ⊩⟨ ∞ ⟩ t ≡ t' ∷ A ^ [ r , ι ⁰ ] / [A])
         ([Id] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]) →
         ([Id'] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ]) →
         ([e] : Γ ⊩⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Id] ) →
         ([e'] : Γ ⊩⟨ ∞ ⟩ e' ∷ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ] / [Id'] ) →
         Γ ⊩⟨ ∞ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ r , ι ⁰ ] / [B]
castext∞ {A} {A'} {B} {B'} {r} {t} {t'} {e} {e'} {Γ} ⊢Γ [U] [U'] [AU] [AU'] [BU] [BU'] [UA≡UA'] [UB≡UB'] [A] [A'] [B] [B'] [t] [t'] [t≡t'] [Id] [Id'] [e] [e'] =
  let
    [A]′ : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ]
    [A]′ = univEq [U] [AU]
    [A']′ : Γ ⊩⟨ ι ⁰ ⟩ A' ^ [ r , ι ⁰ ]
    [A']′ = univEq [U] [AU']
    [t]′ : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t]′ = irrelevanceTerm [A] (emb ∞< (emb emb< [A]′)) [t]
    [B]′ : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ]
    [B]′ = univEq [U'] [BU]
    [B']′ : Γ ⊩⟨ ι ⁰ ⟩ B' ^ [ r , ι ⁰ ]
    [B']′ = univEq [U'] [BU']
    [A≡A']′ : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A' ^ [ r , ι ⁰ ] / [A]′
    [A≡A']′ = univEqEq [U] [A]′ [UA≡UA']
    [B≡B']′ : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B' ^ [ r , ι ⁰ ] / [B]′
    [B≡B']′ = univEqEq [U'] [B]′ [UB≡UB']
    [t']′ : Γ ⊩⟨ ι ⁰ ⟩ t' ∷ A' ^ [ r , ι ⁰ ] / [A']′
    [t']′ = irrelevanceTerm [A'] (emb ∞< (emb emb< [A']′)) [t']
    [t≡t']′ : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t' ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t≡t']′ = irrelevanceEqTerm [A] (emb ∞< (emb emb< [A]′)) [t≡t']
    ⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]
    ⊢e = escapeTerm [Id] [e]
    ⊢e' : Γ ⊢ e' ∷ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ]
    ⊢e' = escapeTerm [Id'] [e']
    x : Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ r , ι ⁰ ] / [B]′
    x = proj₁ ([castext] ⊢Γ [A]′ [A']′ [A≡A']′ [B]′ [B']′ [B≡B']′) [t]′ [t']′ [t≡t']′ ⊢e ⊢e'
  in irrelevanceEqTerm (emb ∞< (emb emb< [B]′)) [B] x

castext∞' : ∀ {A A' B B' r t t' e e' Γ}
         (⊢Γ : ⊢ Γ)
         ([U] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([U'] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([AU] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([AU'] : Γ ⊩⟨ ∞ ⟩ A' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U'])
         ([BU] : Γ ⊩⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([BU'] : Γ ⊩⟨ ∞ ⟩ B' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U'])
         ([UA≡UA'] : Γ ⊩⟨ ∞ ⟩ A ≡ A' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([UB≡UB'] : Γ ⊩⟨ ∞ ⟩ B ≡ B' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([A] : Γ ⊩⟨ ∞ ⟩ A ^ [ r , ι ⁰ ])
         ([A'] : Γ ⊩⟨ ∞ ⟩ A' ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ∞ ⟩ B ^ [ r , ι ⁰ ])
         ([B'] : Γ ⊩⟨ ∞ ⟩ B' ^ [ r , ι ⁰ ])
         ([t] : Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         ([t'] : Γ ⊩⟨ ∞ ⟩ t' ∷ A' ^ [ r , ι ⁰ ] / [A'])
         ([t≡t'] : Γ ⊩⟨ ∞ ⟩ t ≡ t' ∷ A ^ [ r , ι ⁰ ] / [A])
         ([Id] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]) →
         ([Id'] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ]) →
         ([e] : Γ ⊩⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Id] ) →
         ([e'] : Γ ⊩⟨ ∞ ⟩ e' ∷ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ] / [Id'] ) →
         Γ ⊩⟨ ∞ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ r , ι ⁰ ] / [B]
castext∞' {A} {A'} {B} {B'} {r} {t} {t'} {e} {e'} {Γ} ⊢Γ [U] [U'] [AU] [AU'] [BU] [BU'] [UA≡UA'] [UB≡UB'] [A] [A'] [B] [B'] [t] [t'] [t≡t'] [Id] [Id'] [e] [e'] =
  let
    [A]′ : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ]
    [A]′ = univEq [U] [AU]
    [A']′ : Γ ⊩⟨ ι ⁰ ⟩ A' ^ [ r , ι ⁰ ]
    [A']′ = univEq [U'] [AU']
    [t]′ : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t]′ = irrelevanceTerm [A] (emb ∞< (emb emb< [A]′)) [t]
    [B]′ : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ]
    [B]′ = univEq [U] [BU]
    [B']′ : Γ ⊩⟨ ι ⁰ ⟩ B' ^ [ r , ι ⁰ ]
    [B']′ = univEq [U'] [BU']
    [A≡A']′ : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A' ^ [ r , ι ⁰ ] / [A]′
    [A≡A']′ = univEqEq [U] [A]′ [UA≡UA']
    [B≡B']′ : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B' ^ [ r , ι ⁰ ] / [B]′
    [B≡B']′ = univEqEq [U] [B]′ [UB≡UB']
    [t']′ : Γ ⊩⟨ ι ⁰ ⟩ t' ∷ A' ^ [ r , ι ⁰ ] / [A']′
    [t']′ = irrelevanceTerm [A'] (emb ∞< (emb emb< [A']′)) [t']
    [t≡t']′ : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t' ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t≡t']′ = irrelevanceEqTerm [A] (emb ∞< (emb emb< [A]′)) [t≡t']
    ⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]
    ⊢e = escapeTerm [Id] [e]
    ⊢e' : Γ ⊢ e' ∷ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ]
    ⊢e' = escapeTerm [Id'] [e']
    x : Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ r , ι ⁰ ] / [B]′
    x = proj₁ ([castext] ⊢Γ [A]′ [A']′ [A≡A']′ [B]′ [B']′ [B≡B']′) [t]′ [t']′ [t≡t']′ ⊢e ⊢e'
  in irrelevanceEqTerm (emb ∞< (emb emb< [B]′)) [B] x

abstract

  castᵗᵛ : ∀ {A B r t e Γ}
           ([Γ] : ⊩ᵛ Γ)
           ([U] : Γ ⊩ᵛ⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ])
           ([AU] : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
           ([BU] : Γ ⊩ᵛ⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
           ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ r , ι ⁰ ] / [Γ])
           ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ [ r , ι ⁰ ] / [Γ])
           ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [Γ] / [A])
           ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Γ]) →
           ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Γ] / [Id] ) →
           Γ ⊩ᵛ⟨ ∞ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [Γ] / [B]
  castᵗᵛ {A} {B} {t} {e} {Γ} [Γ] [U] [AU] [BU] [A] [B] [t] [Id] [e] ⊢Δ [σ] =
    cast∞ ⊢Δ (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([AU] ⊢Δ [σ])) (proj₁ ([BU] ⊢Δ [σ]))
      (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ]))
      (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([Id] ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ]))
    , λ [σ′] [σ≡σ′] → castext∞' ⊢Δ (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([U] ⊢Δ [σ′]))
      (proj₁ ([AU] ⊢Δ [σ])) (proj₁ ([AU] ⊢Δ [σ′])) (proj₁ ([BU] ⊢Δ [σ])) (proj₁ ([BU] ⊢Δ [σ′]))
      (proj₂ ([AU] ⊢Δ [σ]) [σ′] [σ≡σ′]) (proj₂ ([BU] ⊢Δ [σ]) [σ′] [σ≡σ′])
      (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ′]))
      (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ′]))
      (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ′])) (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
      (proj₁ ([Id] ⊢Δ [σ])) (proj₁ ([Id] ⊢Δ [σ′])) (proj₁ ([e] ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ′]))

  cast-congᵗᵛ : ∀ {A A' B B' t t' e e' r Γ}
              ([Γ] : ⊩ᵛ Γ) →
              ([U] : Γ ⊩ᵛ⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ])
              ([U'] : Γ ⊩ᵛ⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ])
              ([AU] : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
              ([AU'] : Γ ⊩ᵛ⟨ ∞ ⟩ A' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
              ([BU] : Γ ⊩ᵛ⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U'])
              ([BU'] : Γ ⊩ᵛ⟨ ∞ ⟩ B' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U'])
              ([UA≡UA'] : Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ A' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
              ([UB≡UB'] : Γ ⊩ᵛ⟨ ∞ ⟩ B ≡ B' ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U'])
              ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ r , ι ⁰ ] / [Γ])
              ([A'] : Γ ⊩ᵛ⟨ ∞ ⟩ A' ^ [ r , ι ⁰ ] / [Γ])
              ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ [ r , ι ⁰ ] / [Γ])
              ([B'] : Γ ⊩ᵛ⟨ ∞ ⟩ B' ^ [ r , ι ⁰ ] / [Γ])
              ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [Γ] / [A])
              ([t'] : Γ ⊩ᵛ⟨ ∞ ⟩ t' ∷ A' ^ [ r , ι ⁰ ] / [Γ] / [A'])
              ([t≡t']ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t' ∷ A ^ [ r , ι ⁰ ] / [Γ] / [A] )
              ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Γ])
              ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Γ] / [Id] )
              ([Id'] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ] / [Γ])
              ([e'] : Γ ⊩ᵛ⟨ ∞ ⟩ e' ∷ Id (Univ r ⁰) A' B' ^ [ % , ι ⁰ ] / [Γ] / [Id'] ) →
              Γ ⊩ᵛ⟨ ∞ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ r , ι ⁰ ] / [Γ] / [B]
  cast-congᵗᵛ [Γ] [U] [U'] [AU] [AU'] [BU] [BU'] [UA≡UA'] [UB≡UB'] [A] [A'] [B]
              [B'] [t] [t'] [t≡t']ₜ [Id] [e] [Id'] [e'] ⊢Δ [σ] =
    castext∞ ⊢Δ (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([U'] ⊢Δ [σ]))
      (proj₁ ([AU] ⊢Δ [σ])) (proj₁ ([AU'] ⊢Δ [σ])) (proj₁ ([BU] ⊢Δ [σ])) (proj₁ ([BU'] ⊢Δ [σ])) ([UA≡UA'] ⊢Δ [σ]) ([UB≡UB'] ⊢Δ [σ])
      (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([A'] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ])) (proj₁ ([B'] ⊢Δ [σ]))
      (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t'] ⊢Δ [σ])) ([t≡t']ₜ ⊢Δ [σ])
      (proj₁ ([Id] ⊢Δ [σ])) (proj₁ ([Id'] ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ])) (proj₁ ([e'] ⊢Δ [σ]))
