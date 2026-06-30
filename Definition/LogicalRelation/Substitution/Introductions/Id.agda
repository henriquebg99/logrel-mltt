{-# OPTIONS --safe #-}


import Definition.Equiv as E
import Definition.Typed.EqualityRelation as ER
module Definition.LogicalRelation.Substitution.Introductions.Id (equiv : E.Equiv) {{eqrel : ER.EqRelSet equiv}} where
open import Definition.Typed.EqualityRelation equiv
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed equiv
open import Definition.Typed.Properties equiv
import Definition.Typed.Weakening equiv as Twk
open import Definition.Typed.RedSteps equiv
open import Definition.LogicalRelation equiv
open import Definition.LogicalRelation.Irrelevance equiv
open import Definition.LogicalRelation.ShapeView equiv
open import Definition.LogicalRelation.Properties equiv
open import Definition.LogicalRelation.Application equiv
open import Definition.LogicalRelation.Substitution equiv
import Definition.LogicalRelation.Weakening equiv as Lwk
open import Definition.LogicalRelation.Substitution.Properties equiv
import Definition.LogicalRelation.Substitution.Irrelevance equiv as S
open import Definition.LogicalRelation.Substitution.Reflexivity equiv
open import Definition.LogicalRelation.Substitution.Weakening equiv
open import Definition.LogicalRelation.Substitution.Introductions.Empty equiv
open import Definition.LogicalRelation.Substitution.Introductions.Pi equiv
open import Definition.LogicalRelation.Substitution.MaybeEmbed equiv
open import Definition.LogicalRelation.Substitution.Introductions.Universe equiv

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE

-- Validity of Id.
Idᵛ-min : ∀ {A t u Γ l}
     ([Γ] : ⊩ᵛ Γ)
     ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
   → ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
   → ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
   → Γ ⊩ᵛ⟨ ι ⁰ ⟩ Id A t u ^ [ % , ι ⁰ ] / [Γ]
Idᵛ-min {A} {t} {u} {Γ} {l} [Γ] [A] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [A]σ {σ′} [σ′] = [A] {σ = σ′} ⊢Δ [σ′]
      [σA] = proj₁ ([A]σ [σ])
      ⊢A {σ′} [σ′] = escape (proj₁ ([A]σ {σ′} [σ′]))
      ⊢A≡A = escapeEq [σA] (reflEq [σA])
      [t]σ {σ′} [σ′] = [t] {σ = σ′} ⊢Δ [σ′]
      [σt] = proj₁ ([t]σ [σ])
      ⊢t {σ′} [σ′] = escapeTerm (proj₁ ([A]σ {σ′} [σ′])) (proj₁ ([t]σ {σ′} [σ′]))
      ⊢t≡t = escapeTermEq [σA] (reflEqTerm [σA] [σt])
      [u]σ {σ′} [σ′] = [u] {σ = σ′} ⊢Δ [σ′]
      [σu] = proj₁ ([u]σ [σ])
      ⊢u {σ′} [σ′] = escapeTerm (proj₁ ([A]σ {σ′} [σ′])) (proj₁ ([u]σ {σ′} [σ′]))
      ⊢u≡u = escapeTermEq [σA] (reflEqTerm [σA] [σu])
      ⊢IdA = Idⱼ (un-univ (⊢A [σ])) (⊢t [σ]) (⊢u [σ])
  in Idᵣ′ (subst σ A) (subst σ t) (subst σ u) l (idRed:*: (univ ⊢IdA))
          (⊢A [σ]) (⊢t [σ]) (⊢u [σ]) (≅-univ (≅ₜ-Id-cong (≅-un-univ ⊢A≡A) ⊢t≡t ⊢u≡u))

     , λ {σ′} [σ′] [σ≡σ′] →
        let [wk1σ] = wk1SubstS [Γ] ⊢Δ (⊢A [σ]) [σ]
            [wk1σ′] = wk1SubstS [Γ] ⊢Δ (⊢A [σ]) [σ′]
            [wk1σ≡wk1σ′] = wk1SubstSEq [Γ] ⊢Δ (⊢A [σ]) [σ] [σ≡σ′]
        in  Id₌ _ _ _ (id (univ (Idⱼ (un-univ (⊢A [σ′])) (⊢t [σ′]) (⊢u [σ′]))))
               (≅-univ (≅ₜ-Id-cong
                                  (≅-un-univ (escapeEq (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′])))
                                  (escapeTermEq (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]))
                                  (escapeTermEq (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]))))

Idᵛ : ∀ {A t u Γ l}
     ([Γ] : ⊩ᵛ Γ)
     ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
   → ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
   → ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
   → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ^ [ % , ι ⁰ ] / [Γ]
Idᵛ {A} {t} {u} {Γ} {l} [Γ] [A] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [A]σ {σ′} [σ′] = [A] {σ = σ′} ⊢Δ [σ′]
      [σA] = proj₁ ([A]σ [σ])
      ⊢A {σ′} [σ′] = escape (proj₁ ([A]σ {σ′} [σ′]))
      ⊢A≡A = escapeEq [σA] (reflEq [σA])
      [t]σ {σ′} [σ′] = [t] {σ = σ′} ⊢Δ [σ′]
      [σt] = proj₁ ([t]σ [σ])
      ⊢t {σ′} [σ′] = escapeTerm (proj₁ ([A]σ {σ′} [σ′])) (proj₁ ([t]σ {σ′} [σ′]))
      ⊢t≡t = escapeTermEq [σA] (reflEqTerm [σA] [σt])
      [u]σ {σ′} [σ′] = [u] {σ = σ′} ⊢Δ [σ′]
      [σu] = proj₁ ([u]σ [σ])
      ⊢u {σ′} [σ′] = escapeTerm (proj₁ ([A]σ {σ′} [σ′])) (proj₁ ([u]σ {σ′} [σ′]))
      ⊢u≡u = escapeTermEq [σA] (reflEqTerm [σA] [σu])
      ⊢IdA = Idⱼ (un-univ (⊢A [σ])) (⊢t [σ]) (⊢u [σ])
  in Idᵣ′ (subst σ A) (subst σ t) (subst σ u) l (idRed:*: (univ ⊢IdA))
          (⊢A [σ]) (⊢t [σ]) (⊢u [σ]) (≅-univ (≅ₜ-Id-cong (≅-un-univ ⊢A≡A) ⊢t≡t ⊢u≡u))

     , λ {σ′} [σ′] [σ≡σ′] →
        let [wk1σ] = wk1SubstS [Γ] ⊢Δ (⊢A [σ]) [σ]
            [wk1σ′] = wk1SubstS [Γ] ⊢Δ (⊢A [σ]) [σ′]
            [wk1σ≡wk1σ′] = wk1SubstSEq [Γ] ⊢Δ (⊢A [σ]) [σ] [σ≡σ′]
        in  Id₌ _ _ _ (id (univ (Idⱼ (un-univ (⊢A [σ′])) (⊢t [σ′]) (⊢u [σ′]))))
               (≅-univ (≅ₜ-Id-cong
                                  (≅-un-univ (escapeEq (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′])))
                                  (escapeTermEq (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]))
                                  (escapeTermEq (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]))))

Idᵗᵛ-min : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ next ⁰ ⟩ Id A t u ∷ SProp ^ [ ! , next ⁰ ] / [Γ] / Uᵛgen (≡is≤ PE.refl) <next [Γ]
Idᵗᵛ-min {A} {t} {u} {_} {l} [Γ] [A] [t] [u] =
  let [U] = Uᵛgen (≡is≤ PE.refl) <next [Γ]
  in un-univᵛ {A = Id A t u} [Γ] [U] (Idᵛ-min {A} {t} {u} [Γ] [A] [t] [u])

Idᵗᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ) →
       let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
           [U] = maybeEmbᵛ {A = SProp} [Γ] (Uᵛ <next [Γ])
       in ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
          ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([A]t : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ∷ SProp ^ [ ! , next ⁰ ] / [Γ] / [U]
Idᵗᵛ {A} {t} {u} {_} {l} [Γ] [A] [t] [u] [A]t =
  let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
      [A]' = univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]t
      [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ] [A] [A]' [t]
      [u]' = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ] [A] [A]' [u]
      [Id] = Idᵗᵛ-min {A} {t} {u} [Γ] [A]' [t]' [u]'
  in maybeEmbTermᵛ {l = next ⁰} {A = SProp} {t = Id A t u} [Γ] (Uᵛgen (≡is≤ PE.refl) <next [Γ]) [Id]


Id-congᵛ-min : ∀ {A A' t t' u u' Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([A'] : Γ ⊩ᵛ⟨ ι l ⟩ A' ^ [ ! , ι l ] / [Γ])
       ([t'] : Γ ⊩ᵛ⟨ ι l ⟩ t' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([u'] : Γ ⊩ᵛ⟨ ι l ⟩ u' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([A≡A'] : Γ ⊩ᵛ⟨ ι l ⟩ A ≡ A' ^ [ ! , ι l ] / [Γ] / [A])
       ([t≡t'] : Γ ⊩ᵛ⟨ ι l ⟩ t ≡ t' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u≡u'] : Γ ⊩ᵛ⟨ ι l ⟩ u ≡ u' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ι ⁰ ⟩ Id A t u ≡ Id A' t' u' ^ [ % , ι ⁰ ] / [Γ] / Idᵛ-min {A} {t} {u} [Γ] [A] [t] [u]
Id-congᵛ-min {A} {A'} {t} {t'} {u} {u'} [Γ] [A] [t] [u] [A'] [t'] [u'] [A≡A'] [t≡t'] [u≡u'] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [Id] = Idᵛ-min {A} {t} {u} [Γ] [A] [t] [u]
      [σId] = proj₁ ([Id] ⊢Δ [σ])
      _ , Idᵣ A′ t′ u′ _ D′ ⊢A′ ⊢t′ ⊢u′ A≡A′ = extractMaybeEmb (Id-elim [σId])
      [σA] = proj₁ ([A] ⊢Δ [σ])
      [σA'] = proj₁ ([A'] ⊢Δ [σ])
      ⊢σA = escape [σA]
      ⊢σA' = escape [σA']
      ⊢σA≡σA' = escapeEq [σA] ([A≡A'] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      ⊢σt = escapeTerm [σA] [σt]
      ⊢σt' = escapeTerm [σA'] (proj₁ ([t'] ⊢Δ [σ]))
      ⊢σt≡σt' = escapeTermEq [σA] ([t≡t'] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      ⊢σu = escapeTerm [σA] [σu]
      ⊢σu' = escapeTerm [σA'] (proj₁ ([u'] ⊢Δ [σ]))
      ⊢σu≡σu' = escapeTermEq [σA] ([u≡u'] ⊢Δ [σ])
  in  Id₌ (subst σ A') (subst σ t') (subst σ u')
         (id (univ (Idⱼ (un-univ ⊢σA') ⊢σt' ⊢σu')))
         (≅-univ (≅ₜ-Id-cong (≅-un-univ ⊢σA≡σA') ⊢σt≡σt' ⊢σu≡σu'))

Id-cong-minᵗᵛ : ∀ {A A' t t' u u' Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([A'] : Γ ⊩ᵛ⟨ ι l ⟩ A' ^ [ ! , ι l ] / [Γ])
       ([t'] : Γ ⊩ᵛ⟨ ι l ⟩ t' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([u'] : Γ ⊩ᵛ⟨ ι l ⟩ u' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([A≡A'] : Γ ⊩ᵛ⟨ ι l ⟩ A ≡ A' ^ [ ! , ι l ] / [Γ] / [A])
       ([t≡t'] : Γ ⊩ᵛ⟨ ι l ⟩ t ≡ t' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u≡u'] : Γ ⊩ᵛ⟨ ι l ⟩ u ≡ u' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ next ⁰ ⟩ Id A t u ≡ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ] / [Γ] / Uᵛgen (≡is≤ PE.refl) <next [Γ]
Id-cong-minᵗᵛ {A} {A'} {t} {t'} {u} {u'} [Γ] [A] [t] [u] [A'] [t'] [u'] [A≡A'] [t≡t'] [u≡u'] =
  let [U] = Uᵛgen (≡is≤ PE.refl) <next [Γ]
  in un-univEqᵛ {A = Id A t u} {B = Id A' t' u'} [Γ] [U]
                (Idᵛ-min {A} {t} {u} [Γ] [A] [t] [u])
                (Idᵛ-min {A'} {t'} {u'} [Γ] [A'] [t'] [u'])
                (Id-congᵛ-min {A} {A'} {t} {t'} {u} {u'} [Γ] [A] [t] [u] [A'] [t'] [u'] [A≡A'] [t≡t'] [u≡u'])

Id-congᵗᵛ : ∀ {A A' t t' u u' Γ l}
       ([Γ] : ⊩ᵛ Γ) →
       let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
           [U] = maybeEmbᵛ {A = SProp} [Γ] (Uᵛ <next [Γ])
       in ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
          ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([A]t : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          ([A'] : Γ ⊩ᵛ⟨ ∞ ⟩ A' ^ [ ! , ι l ] / [Γ])
          ([t'] : Γ ⊩ᵛ⟨ ∞ ⟩ t' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
          ([u'] : Γ ⊩ᵛ⟨ ∞ ⟩ u' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
          ([A']t : Γ ⊩ᵛ⟨ ∞ ⟩ A' ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          ([A≡A']t : Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ A' ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          ([t≡t'] : Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([u≡u'] : Γ ⊩ᵛ⟨ ∞ ⟩ u ≡ u' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ≡ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ] / [Γ] / [U]
Id-congᵗᵛ {A} {A'} {t} {t'} {u} {u'} {_} {l} [Γ] [A] [t] [u] [A]t [A'] [t'] [u'] [A']t [A≡A']t [t≡t'] [u≡u'] =
   let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
       [A]' = univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]t
       [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ] [A] [A]' [t]
       [u]' = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ] [A] [A]' [u]
       [A']' = univᵛ {A = A'} [Γ] (≡is≤ PE.refl) [UA] [A']t
       [t']' = S.irrelevanceTerm {A = A'} {t = t'} [Γ] [Γ] [A'] [A']' [t']
       [u']' = S.irrelevanceTerm {A = A'} {t = u'} [Γ] [Γ] [A'] [A']' [u']
       [A≡A']' = univEqᵛ {A = A} {B = A'} [Γ] [UA] [A]' [A≡A']t
       [t≡t']' = S.irrelevanceEqTerm {A = A} {t = t} {u = t'} [Γ] [Γ] [A] [A]' [t≡t']
       [u≡u']' = S.irrelevanceEqTerm {A = A} {t = u} {u = u'} [Γ] [Γ] [A] [A]' [u≡u']
       [Id] = Id-cong-minᵗᵛ {A} {A'} {t} {t'} {u} {u'} [Γ] [A]' [t]' [u]' [A']' [t']' [u']' [A≡A']' [t≡t']' [u≡u']'
   in maybeEmbEqTermᵛ {l = next ⁰} {A = SProp} {t = Id A t u} {u = Id A' t' u'} [Γ] (Uᵛgen (≡is≤ PE.refl) <next [Γ]) [Id]
