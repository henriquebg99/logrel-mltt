import Definition.Equiv as E
module Definition.LogicalRelation.Substitution.Introductions.Natrec2 where
open import Definition.Typed.EqualityRelation
open EqRelSet {{...}}
open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Introductions.Nat2
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE
-- Natural recursion closure reduction (requires reducible terms and equality).
natrec2-subst* : ∀ {Γ C c g n n′ l lC} → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊢ C ^ [ ! , ι lC ] → Γ ⊢ c ∷ C [ zero2 ] ^ [ ! , ι lC ]
              → Γ ⊢ g ∷ Π ℕ2 ^ ! ° ⁰ ▹ (C ^ ! ° lC ▹▹ C [ suc2 (var 0) ]↑ ° lC ° lC ^ !) ° lC ° lC ^ ! ^ [ ! , ι lC ] 
              → Γ ⊢ n ⇒* n′ ∷ ℕ2 ^ ι ⁰ 
              → ([ℕ2] : Γ ⊩⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ])
              → Γ ⊩⟨ l ⟩ n′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
              → (∀ {t t′} → Γ ⊩⟨ l ⟩ t  ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
                          → Γ ⊩⟨ l ⟩ t′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
                          → Γ ⊩⟨ l ⟩ t ≡ t′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / [ℕ2]
                          → Γ ⊢ C [ t ] ≡ C [ t′ ] ^ [ ! , ι lC ])
              → Γ ⊢ natrec2 lC C c g n ⇒* natrec2 lC C c g n′ ∷ C [ n ] ^ ι lC
natrec2-subst* C c g (id x) [ℕ2] [n′] prop = id (natrec2ⱼ (λ x → ⊥-elim (!≢% x)) C c g x)
natrec2-subst* C c g (x ⇨ n⇒n′) [ℕ2] [n′] prop =
  let q , w = redSubst*Term n⇒n′ [ℕ2] [n′]
      a , s = redSubstTerm x [ℕ2] q
  in  natrec2-subst C c g x ⇨ conv* (natrec2-subst* C c g n⇒n′ [ℕ2] [n′] prop)
                   (prop q a (symEqTerm [ℕ2] s))


-- Helper functions for construction of valid type for the successor case of natrec2.

suc2Case₃ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ)
           ([ℕ2] : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
         → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ suc2 (var 0) ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] ∙ [ℕ2]
                 / (λ {Δ} {σ} → wk1ᵛ {ℕ2} {ℕ2} [Γ] [ℕ2] [ℕ2] {Δ} {σ})
suc2Case₃ {Γ} {l} [Γ] [ℕ2] {Δ} {σ} =
  suc2ᵛ {n = var 0} {l = l} (_∙_ {A = ℕ2} [Γ] [ℕ2])
       (λ {Δ} {σ} → wk1ᵛ {ℕ2} {ℕ2} [Γ] [ℕ2] [ℕ2] {Δ} {σ})
       (λ ⊢Δ [σ] → proj₂ [σ] , (λ [σ′] [σ≡σ′] → proj₂ [σ≡σ′])) {Δ} {σ}

suc2Case₂ : ∀ {F rF Γ l}
           ([Γ] : ⊩ᵛ Γ)
           ([ℕ2] : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
           ([F] : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ rF / [Γ] ∙ [ℕ2])
         → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F [ suc2 (var 0) ]↑ ^ rF / [Γ] ∙ [ℕ2]
suc2Case₂ {F} {rF} {Γ} {l} [Γ] [ℕ2] [F] =
  subst↑S {ℕ2} {F} {suc2 (var 0)} {F' = ℕ2} [Γ] [ℕ2] [ℕ2] [F]
          (λ {Δ} {σ} → suc2Case₃ [Γ] [ℕ2] {Δ} {σ})

suc2Case₂' : ∀ {F Γ l lF}
           ([Γ] : ⊩ᵛ Γ)
           ([ℕ2] : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
           ([F] : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ ! , ι lF ] / [Γ] ∙ [ℕ2])
         → Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ ! ^ [ ! , ι lF ] / [Γ]
suc2Case₂' {F} {Γ} {l} {lF} [Γ] [ℕ2] [F] =  Πᵛ {ℕ2} {F [ suc2 (var 0) ]↑} (⁰min lF) (≡is≤ PE.refl) [Γ] [ℕ2]
     (suc2Case₂ {F} [Γ] [ℕ2] [F])

suc2Case₁ : ∀ {F rF Γ l lF}
           (rFlF : rF PE.≡ % → lF PE.≡ ⁰)
           ([Γ] : ⊩ᵛ Γ)
           ([ℕ2] : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
           ([F] : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2])
         → Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2]
suc2Case₁ {F} {rF = !} {Γ} {l} _ [Γ] [ℕ2] [F] =
  ▹▹ᵛ {F} {F [ suc2 (var 0) ]↑} (≡is≤ PE.refl) (≡is≤ PE.refl) (_∙_ {A = ℕ2} [Γ] [ℕ2]) [F]
      (suc2Case₂ {F} [Γ] [ℕ2] [F])
suc2Case₁ {F} {rF = %} {Γ} {l} {lF = ⁰} _ [Γ] [ℕ2] [F] =
  ▹▹irrᵛ {F} {F [ suc2 (var 0) ]↑} (_∙_ {A = ℕ2} [Γ] [ℕ2]) [F] (suc2Case₂ {F} [Γ] [ℕ2] [F])
suc2Case₁ {F} {rF = %} {Γ} {l} {lF = ¹} rFlF [Γ] [ℕ2] [F] = ⊥-elim (⁰≢¹ (PE.sym (rFlF PE.refl)))

-- Construct a valid type for the successor case of natrec2.
suc2Case : ∀ {F rF Γ l lF}
          (rFlF : rF PE.≡ % → lF PE.≡ ⁰)
          ([Γ] : ⊩ᵛ Γ)
          ([ℕ2] : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
          ([F] : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2])
        → Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ]
suc2Case {F} {rF = !} {Γ} {l} {lF} rFlF [Γ] [ℕ2] [F] =
  Πᵛ {ℕ2} {F ^ ! ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ !} (⁰min lF) (≡is≤ PE.refl) [Γ] [ℕ2]
     (suc2Case₁ {F} rFlF [Γ] [ℕ2] [F])
suc2Case {F} {rF = %} {Γ} {l} {lF = ⁰} rFlF [Γ] [ℕ2] [F] =
  Πirrᵛ {ℕ2} {F ^ % ° ⁰ ▹▹ F [ suc2 (var 0) ]↑ ° ⁰ ° ⁰ ^ %} [Γ] [ℕ2] (suc2Case₁ {F} rFlF [Γ] [ℕ2] [F])
suc2Case {F} {rF = %} {Γ} {l} {lF = ¹} rFlF [Γ] [ℕ2] [F] = ⊥-elim (⁰≢¹ (PE.sym (rFlF PE.refl)))


-- Construct a valid type equality for the successor case of natrec2.
suc2CaseCong : ∀ {F F′ rF Γ l lF}
              (rFlF : rF PE.≡ % → lF PE.≡ ⁰)
              ([Γ] : ⊩ᵛ Γ)
              ([ℕ2] : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
              ([F] : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2])
              ([F′] : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F′ ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2])
              ([F≡F′] : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2] / [F])
        → Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F  [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF
                  ≡ Π ℕ2 ^ ! ° ⁰ ▹ (F′ ^ rF ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ]
                  / [Γ] / suc2Case {F} rFlF [Γ] [ℕ2] [F]
suc2CaseCong {F} {F′} {rF = !} {Γ} {l} {lF} rFlF [Γ] [ℕ2] [F] [F′] [F≡F′] =
  Π-congᵛ {ℕ2} {F ^ ! ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ !} {ℕ2} {F′ ^ ! ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF ° lF ^ !}
          (⁰min lF) (≡is≤ PE.refl) [Γ] [ℕ2] (suc2Case₁ {F} rFlF [Γ] [ℕ2] [F]) [ℕ2] (suc2Case₁ {F′} rFlF [Γ] [ℕ2] [F′])
          (reflᵛ {ℕ2} [Γ] [ℕ2])
          (▹▹-congᵛ {F} {F′} {F [ suc2 (var 0) ]↑} {F′ [ suc2 (var 0) ]↑} (≡is≤ PE.refl) (≡is≤ PE.refl)
             (_∙_ {A = ℕ2} [Γ] [ℕ2]) [F] [F′] [F≡F′]
             (suc2Case₂ {F} [Γ] [ℕ2] [F]) (suc2Case₂ {F′} [Γ] [ℕ2] [F′])
             (subst↑SEq {ℕ2} {F} {F′} {suc2 (var 0)} {suc2 (var 0)}
                        [Γ] [ℕ2] [F] [F′] [F≡F′]
                        (λ {Δ} {σ} → suc2Case₃ [Γ] [ℕ2] {Δ} {σ})
                        (λ {Δ} {σ} → suc2Case₃ [Γ] [ℕ2] {Δ} {σ})
                        (λ {Δ} {σ} →
                           reflᵗᵛ {ℕ2} {suc2 (var 0)} (_∙_ {A = ℕ2} [Γ] [ℕ2])
                                  (λ {Δ} {σ} → wk1ᵛ {ℕ2} {ℕ2} [Γ] [ℕ2] [ℕ2] {Δ} {σ})
                                  (λ {Δ} {σ} → suc2Case₃ [Γ] [ℕ2] {Δ} {σ})
                           {Δ} {σ})))

suc2CaseCong {F} {F′} {rF = %} {Γ} {l} {lF = ⁰} rFlF [Γ] [ℕ2] [F] [F′] [F≡F′] =
  Πirr-congᵛ {ℕ2} {F ^ % ° ⁰ ▹▹ F [ suc2 (var 0) ]↑ ° ⁰ ° ⁰ ^ %} {ℕ2} {F′ ^ % ° ⁰ ▹▹ F′ [ suc2 (var 0) ]↑ ° ⁰ ° ⁰ ^ %}
          [Γ] [ℕ2] (suc2Case₁ {F} rFlF [Γ] [ℕ2] [F]) [ℕ2] (suc2Case₁ {F′} rFlF [Γ] [ℕ2] [F′])
          (reflᵛ {ℕ2} [Γ] [ℕ2])
          (▹▹irr-congᵛ {F} {F′} {F [ suc2 (var 0) ]↑} {F′ [ suc2 (var 0) ]↑} 
             (_∙_ {A = ℕ2} [Γ] [ℕ2]) [F] [F′] [F≡F′]
             (suc2Case₂ {F} [Γ] [ℕ2] [F]) (suc2Case₂ {F′} [Γ] [ℕ2] [F′])
             (subst↑SEq {ℕ2} {F} {F′} {suc2 (var 0)} {suc2 (var 0)}
                        [Γ] [ℕ2] [F] [F′] [F≡F′]
                        (λ {Δ} {σ} → suc2Case₃ [Γ] [ℕ2] {Δ} {σ})
                        (λ {Δ} {σ} → suc2Case₃ [Γ] [ℕ2] {Δ} {σ})
                        (λ {Δ} {σ} →
                           reflᵗᵛ {ℕ2} {suc2 (var 0)} (_∙_ {A = ℕ2} [Γ] [ℕ2])
                                  (λ {Δ} {σ} → wk1ᵛ {ℕ2} {ℕ2} [Γ] [ℕ2] [ℕ2] {Δ} {σ})
                                  (λ {Δ} {σ} → suc2Case₃ [Γ] [ℕ2] {Δ} {σ})
                           {Δ} {σ})))

suc2CaseCong {F} {F′} {rF = %} {Γ} {l} {lF = ¹} rFlF [Γ] [ℕ2] [F] [F′] [F≡F′] = ⊥-elim (⁰≢¹ (PE.sym (rFlF PE.refl)))

-- Reducibility of natural2 recursion under a valid substitution.
natrec2Term : ∀ {F rF lF z s n Γ Δ σ l}
             (rFlF : rF PE.≡ % → lF PE.≡ ⁰)
             ([Γ]  : ⊩ᵛ Γ)
             ([F]  : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / _∙_ {l = l} [Γ] (ℕ2ᵛ [Γ]))
             ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero2 ] ^ [ rF , ι lF ] / [Γ])
             ([F₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ])
             ([z]  : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F₀])
             ([s]  : Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ]
                       / [Γ] / [F₊])
             (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σn] : Δ ⊩⟨ l ⟩ n ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ))))
           → Δ ⊩⟨ l ⟩ natrec2 lF (subst (liftSubst σ) F) (subst σ z) (subst σ s) n
               ∷ subst (liftSubst σ) F [ n ] ^ [ rF , ι lF ]
               / irrelevance′ (PE.sym (singleSubstComp n σ F))
                              (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrec2Term {F} {rF = !} {lF} {z} {s} {n} {Γ} {Δ} {σ} {l} rFlF [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕ2ₜ .(suc2 m) d n≡n (suc2ᵣ {m} [m])) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      ⊢F = escape (proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢m = escapeTerm {l = l} [σℕ] [m]
      [σsm] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σℕ]
                              (ℕ2ₜ (suc2 m) (idRedTerm:*: (suc2ⱼ ⊢m)) n≡n (suc2ᵣ [m]))
      [σn] = ℕ2ₜ (suc2 m) d n≡n (suc2ᵣ [m])
      [σn]′ , [σn≡σsm] = redSubst*Term (redₜ d) [σℕ] [σsm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₛₘ] = irrelevance′ (PE.sym (singleSubstComp (suc2 m) σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [Fₙ≡Fₛₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                 (PE.sym (singleSubstComp (suc2 m) σ F)) PE.refl PE.refl
                                 [σFₙ]′ [σFₙ]
                                 (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsm]))
      [σFₘ] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                             (substSingletonComp F)))
                           (proj₁ ([F] ⊢Δ ([σ] , [m])))
      [σFₛₘ]′ = irrelevance′ (natrec2IrrelevantSubst F z s m σ)
                             (proj₁ ([F] ⊢Δ ([σ] , [σsm])))
      [σF₊ₘ] = substSΠ₁ (proj₁ ([F₊] ⊢Δ [σ])) [σℕ] [m]
      [FF] = proj₁ (suc2Case₁ {F = F} rFlF [Γ] [ℕ2] [F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      natrecM = appTerm PE.refl [σFₘ] [σFₛₘ]′ [σF₊ₘ]
                        (appTerm PE.refl [σℕ] [σF₊ₘ]
                                 (proj₁ ([F₊] ⊢Δ [σ]))
                                 (proj₁ ([s] ⊢Δ [σ])) [m])
                        (natrec2Term {F} { ! } {lF} {z} {s} {m} {σ = σ} rFlF
                                    [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [m]) 
      natrecM′ = irrelevanceTerm′ (PE.trans
                                    (PE.sym (natrec2IrrelevantSubst F z s m σ))
                                    (PE.sym (singleSubstComp (suc2 m) σ F)))
                                  PE.refl PE.refl [σFₛₘ]′ [σFₛₘ] natrecM
      reduction = natrec2-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsm]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , _ ])
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
                  ⇨∷* (conv* (natrec2-suc ⊢m ⊢F ⊢z ⊢s
                              ⇨ id (escapeTerm [σFₛₘ] natrecM′))
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡Fₛₘ]))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] [σFₛₘ] [Fₙ≡Fₛₘ] natrecM′))
natrec2Term {F} {rF = %} {lF} {z} {s} {n} {Γ} {Δ} {σ} {l} rFlF [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕ2ₜ .(suc2 m) d n≡n (suc2ᵣ {m} [m])) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      ⊢F = escape (proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , _ ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢m = escapeTerm {l = l} [σℕ] [m]
      [σn] = ℕ2ₜ (suc2 m) d n≡n (suc2ᵣ [m])
      [σsm] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σℕ]
                              (ℕ2ₜ (suc2 m) (idRedTerm:*: (suc2ⱼ ⊢m)) n≡n (suc2ᵣ [m]))
      [σn]′ , [σn≡σsm] = redSubst*Term (redₜ d) [σℕ] [σsm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [[ ⊢n , _ , _ ]] = d
  in logRelIrr [σFₙ] (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n)

natrec2Term {F} {rF = !} {lF} {z} {s} {n} {Γ} {Δ} {σ} {l} rFlF [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕ2ₜ .zero2 d n≡n zero2ᵣ) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      ⊢F = escape [σF]
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , _ ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      [σ0] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σℕ]
                             (ℕ2ₜ zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) n≡n zero2ᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ2] ⊢Δ [σ])) [σ0]
      [σn] = ℕ2ₜ zero2 d n≡n zero2ᵣ
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [Fₙ≡F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0])
                       (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F)) PE.refl PE.refl
                                [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [Fₙ≡F₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.trans (substConcatSingleton′ F)
                                            (PE.sym (singleSubstComp zero2 σ F))) PE.refl PE.refl 
                                  [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [σz] = proj₁ ([z] ⊢Δ [σ])
      reduction = natrec2-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ2] ⊢Δ [σ])) [σ0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , _ ])
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
                  ⇨∷* (conv* (natrec2-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡F₀]″))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀] [σz]))
natrec2Term {F} {rF = %} {lF} {z} {s} {n} {Γ} {Δ} {σ} {l} rFlF [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕ2ₜ .zero2 d n≡n zero2ᵣ) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      ⊢F = escape [σF]
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , _ ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      [σ0] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σℕ]
                             (ℕ2ₜ zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) n≡n zero2ᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ2] ⊢Δ [σ])) [σ0]
      [σn] = ℕ2ₜ zero2 d n≡n zero2ᵣ
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [[ ⊢n , _ , _ ]] = d
  in logRelIrr [σFₙ] (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n)

natrec2Term {F} {rF = !} {lF} {z} {s} {n} {Γ} {Δ} {σ} {l} rFlF [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕ2ₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      [σn] = ℕ2ₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , _ ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ ! , _ ]) (singleSubstLift F zero2)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢s≡s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                      (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₁ ([s] ⊢Δ [σ]))))
      [σm] = neuTerm [σℕ] neM ⊢m m≡m
      [σn]′ , [σn≡σm] = redSubst*Term (redₜ d) [σℕ] [σm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₘ] = irrelevance′ (PE.sym (singleSubstComp m σ F))
                           (proj₁ ([F] ⊢Δ ([σ] , [σm])))
      [Fₙ≡Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (singleSubstComp m σ F)) PE.refl PE.refl [σFₙ]′ [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn]))) ([σ] , [σm])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σm]))
      natrecM = neuTerm [σFₘ] (natrec2ₙ neM) (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢m)
                        (~-natrec2 ⊢F≡F ⊢z≡z ⊢s≡s m≡m)
      reduction = natrec2-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σm]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , _ ])
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] ,
                                                                [t≡t′])))))
  in  proj₁ (redSubst*Term reduction [σFₙ]
                           (convTerm₂ [σFₙ] [σFₘ] [Fₙ≡Fₘ] natrecM))
natrec2Term {F} {rF = %} {lF} {z} {s} {n} {Γ} {Δ} {σ} {l} rFlF [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ]
           (ℕ2ₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      [σn] = ℕ2ₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , _ ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ % , _ ]) (singleSubstLift F zero2)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢s≡s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                      (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₁ ([s] ⊢Δ [σ]))))
      [σm] = neuTerm [σℕ] neM ⊢m m≡m
      [σn]′ , [σn≡σm] = redSubst*Term (redₜ d) [σℕ] [σm]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [[ ⊢n , _ , _ ]] = d
  in logRelIrr [σFₙ] (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n)




-- Reducibility of natural2 recursion congurence under a valid substitution equality.
natrec2-congTerm : ∀ {F F′ rF lF z z′ s s′ n m Γ Δ σ σ′ l}
                  (rFlF : rF PE.≡ % → lF PE.≡ ⁰)
                  ([Γ]      : ⊩ᵛ Γ)
                  ([F]      : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / _∙_ {l = l} [Γ] (ℕ2ᵛ [Γ]))
                  ([F′]     : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F′ ^ [ rF , ι lF ] / _∙_ {l = l} [Γ] (ℕ2ᵛ [Γ]))
                  ([F≡F′]   : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ [ rF , ι lF ] / _∙_ {l = l} [Γ] (ℕ2ᵛ [Γ])
                                    / [F])
                  ([F₀]     : Γ ⊩ᵛ⟨ l ⟩ F [ zero2 ] ^ [ rF , ι lF ] / [Γ])
                  ([F′₀]    : Γ ⊩ᵛ⟨ l ⟩ F′ [ zero2 ] ^ [ rF , ι lF ] / [Γ])
                  ([F₀≡F′₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero2 ] ≡ F′ [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F₀])
                  ([F₊]     : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF  ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ]
                                / [Γ])
                  ([F′₊]    : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F′ ^ rF ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ]
                                / [Γ])
                  ([F₊≡F₊′] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF  ° lF ^ rF
                                ≡ Π ℕ2 ^ ! ° ⁰ ▹ (F′ ^ rF ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ]
                                / [Γ] / [F₊])
                  ([z]      : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F₀])
                  ([z′]     : Γ ⊩ᵛ⟨ l ⟩ z′ ∷ F′ [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F′₀])
                  ([z≡z′]   : Γ ⊩ᵛ⟨ l ⟩ z ≡ z′ ∷ F [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F₀])
                  ([s]      : Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF  ° lF ^ rF ^ [ rF , ι lF ]
                                / [Γ] / [F₊])
                  ([s′]     : Γ ⊩ᵛ⟨ l ⟩ s′
                                ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F′ ^ rF ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ]
                                / [Γ] / [F′₊])
                  ([s≡s′]   : Γ ⊩ᵛ⟨ l ⟩ s ≡ s′
                                ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ]
                                / [Γ] / [F₊])
                  (⊢Δ       : ⊢ Δ)
                  ([σ]      : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
                  ([σ′]     : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                  ([σ≡σ′]   : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                  ([σn]     : Δ ⊩⟨ l ⟩ n ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ))))
                  ([σm]     : Δ ⊩⟨ l ⟩ m ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ))))
                  ([σn≡σm]  : Δ ⊩⟨ l ⟩ n ≡ m ∷ ℕ2 ^ [ ! , ι ⁰ ] / ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ))))
                → Δ ⊩⟨ l ⟩ natrec2 lF (subst (liftSubst σ) F)
                                  (subst σ z) (subst σ s) n
                    ≡ natrec2 lF (subst (liftSubst σ′) F′)
                             (subst σ′ z′) (subst σ′ s′) m
                    ∷ subst (liftSubst σ) F [ n ] ^ [ rF , ι lF ]
                    / irrelevance′ (PE.sym (singleSubstComp n σ F))
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn])))
natrec2-congTerm {F} {F′} {rF = !} {lF} {z} {z′} {s} {s′} {n} {m} {Γ} {Δ} {σ} {σ′} {l} rFlF
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ .(suc2 n′) d n≡n (suc2ᵣ {n′} [n′]))
                (ℕ2ₜ .(suc2 m′) d′ m≡m (suc2ᵣ {m′} [m′]))
                (ℕ2ₜ₌ .(suc2 n″) .(suc2 m″) d₁ d₁′
                     t≡u (suc2ᵣ {n″} {m″} [n″≡m″])) =
  let n″≡n′ = suc2-PE-injectivity (whrDet*Term (redₜ d₁ , suc2ₙ) (redₜ d , suc2ₙ))
      m″≡m′ = suc2-PE-injectivity (whrDet*Term (redₜ d₁′ , suc2ₙ) (redₜ d′ , suc2ₙ))
      [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      [σ′ℕ2] = proj₁ ([ℕ2] ⊢Δ [σ′])
      [n′≡m′] = irrelevanceEqTerm″ PE.refl PE.refl n″≡n′ m″≡m′ PE.refl [σℕ] [σℕ] [n″≡m″]
      [σn] = ℕ2ₜ (suc2 n′) d n≡n (suc2ᵣ [n′])
      [σ′m] = ℕ2ₜ (suc2 m′) d′ m≡m (suc2ᵣ [m′])
      [σn≡σ′m] = ℕ2ₜ₌ (suc2 n″) (suc2 m″) d₁ d₁′ t≡u (suc2ᵣ [n″≡m″])
      ⊢ℕ2 = escape [σℕ]
      ⊢F = escape (proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n′ = escapeTerm {l = l} [σℕ] [n′]
      ⊢ℕ2′ = escape [σ′ℕ2]
      ⊢F′ = escape (proj₁ ([F′] (⊢Δ ∙ ⊢ℕ2′)
                      (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′])))
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F′ zero2)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                    (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ′ F′ ! lF)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′]))
                                    (proj₁ ([s′] ⊢Δ [σ′])))
      ⊢m′ = escapeTerm {l = l} [σ′ℕ2] [m′]
      [σsn′] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σℕ]
                               (ℕ2ₜ (suc2 n′) (idRedTerm:*: (suc2ⱼ ⊢n′)) n≡n (suc2ᵣ [n′]))
      [σn]′ , [σn≡σsn′] = redSubst*Term (redₜ d) [σℕ] [σsn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₛₙ′] = irrelevance′ (PE.sym (singleSubstComp (suc2 n′) σ F))
                             (proj₁ ([F] ⊢Δ ([σ] , [σsn′])))
      [Fₙ≡Fₛₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.sym (singleSubstComp (suc2 n′) σ F)) PE.refl PE.refl 
                                  [σFₙ]′ [σFₙ]
                                  (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                         (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [Fₙ≡Fₛₙ′]′ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (natrec2IrrelevantSubst F z s n′ σ) PE.refl PE.refl
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                          (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [σFₙ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                              (substSingletonComp F)))
                            (proj₁ ([F] ⊢Δ ([σ] , [n′])))
      [σFₛₙ′]′ = irrelevance′ (natrec2IrrelevantSubst F z s n′ σ)
                              (proj₁ ([F] ⊢Δ ([σ] , [σsn′])))
      [σF₊ₙ′] = substSΠ₁ (proj₁ ([F₊] ⊢Δ [σ])) [σℕ] [n′]
      [σ′sm′] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σ′ℕ2]
                                (ℕ2ₜ (suc2 m′) (idRedTerm:*: (suc2ⱼ ⊢m′)) m≡m (suc2ᵣ [m′]))
      [σ′m]′ , [σ′m≡σ′sm′] = redSubst*Term (redₜ d′) [σ′ℕ2] [σ′sm′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₛₘ′] = irrelevance′ (PE.sym (singleSubstComp (suc2 m′) σ′ F′))
                               (proj₁ ([F′] ⊢Δ ([σ′] , [σ′sm′])))
      [F′ₘ≡F′ₛₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                    (PE.sym (singleSubstComp (suc2 m′) σ′ F′)) PE.refl PE.refl 
                                    [σ′F′ₘ]′ [σ′F′ₘ]
                                    (proj₂ ([F′] ⊢Δ ([σ′] , [σ′m]))
                                           ([σ′] , [σ′sm′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′sm′]))
      [σ′Fₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                               (substSingletonComp F)))
                             (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F′)
                                                (substSingletonComp F′)))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₛₘ′]′ = irrelevance′ (natrec2IrrelevantSubst F′ z′ s′ m′ σ′)
                                (proj₁ ([F′] ⊢Δ ([σ′] , [σ′sm′])))
      [σ′F′₊ₘ′] = substSΠ₁ (proj₁ ([F′₊] ⊢Δ [σ′])) [σ′ℕ2] [m′]
      [σFₙ′≡σ′Fₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp n′ σ F))
                                     (PE.sym (singleSubstComp m′ σ′ F)) PE.refl PE.refl 
                                     (proj₁ ([F] ⊢Δ ([σ] , [n′]))) [σFₙ′]
                                     (proj₂ ([F] ⊢Δ ([σ] , [n′]))
                                            ([σ′] , [m′]) ([σ≡σ′] , [n′≡m′]))
      [σ′Fₘ′≡σ′F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m′ σ′ F))
                                       (PE.sym (singleSubstComp m′ σ′ F′)) PE.refl PE.refl 
                                       (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
                                       [σ′Fₘ′] ([F≡F′] ⊢Δ ([σ′] , [m′]))
      [σFₙ′≡σ′F′ₘ′] = transEq [σFₙ′] [σ′Fₘ′] [σ′F′ₘ′] [σFₙ′≡σ′Fₘ′] [σ′Fₘ′≡σ′F′ₘ′]
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F)) PE.refl PE.refl 
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn]))) [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn]))
                                          ([σ′] , [σ′m]) ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′)) PE.refl PE.refl 
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [FF] = proj₁ (suc2Case₁ {F = F} rFlF [Γ] [ℕ2] [F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      natrecN = appTerm PE.refl [σFₙ′] [σFₛₙ′]′ [σF₊ₙ′]
                        (appTerm PE.refl [σℕ] [σF₊ₙ′] (proj₁ ([F₊] ⊢Δ [σ]))
                                 (proj₁ ([s] ⊢Δ [σ])) [n′])
                        (natrec2Term {F} { ! } {lF} {z} {s} {n′} {σ = σ} rFlF
                                    [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [n′])
      natrecN′ = irrelevanceTerm′ (PE.trans (PE.sym (natrec2IrrelevantSubst F z s n′ σ))
                                            (PE.sym (singleSubstComp (suc2 n′) σ F)))
                                  PE.refl PE.refl [σFₛₙ′]′ [σFₛₙ′] natrecN
      [FF′] = proj₁ (suc2Case₁ {F = F′} rFlF [Γ] [ℕ2] [F′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′]))
      natrecM = appTerm PE.refl [σ′F′ₘ′] [σ′F′ₛₘ′]′ [σ′F′₊ₘ′]
                        (appTerm PE.refl [σ′ℕ2] [σ′F′₊ₘ′] (proj₁ ([F′₊] ⊢Δ [σ′]))
                                 (proj₁ ([s′] ⊢Δ [σ′])) [m′])
                        (natrec2Term {F′} { ! } {lF} {z′} {s′} {m′} {σ = σ′} rFlF
                                    [Γ] [F′] [F′₀] [F′₊] [z′] [s′] ⊢Δ [σ′] [m′])
      natrecM′ = irrelevanceTerm′ (PE.trans (PE.sym (natrec2IrrelevantSubst F′ z′ s′ m′ σ′))
                                            (PE.sym (singleSubstComp (suc2 m′) σ′ F′)))
                                  PE.refl PE.refl [σ′F′ₛₘ′]′ [σ′F′ₛₘ′] natrecM
      [σs≡σ′s] = proj₂ ([s] ⊢Δ [σ]) [σ′] [σ≡σ′]
      [σ′s≡σ′s′] = convEqTerm₂ (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([F₊] ⊢Δ [σ′]))
                               (proj₂ ([F₊] ⊢Δ [σ]) [σ′] [σ≡σ′]) ([s≡s′] ⊢Δ [σ′])
      [σs≡σ′s′] = transEqTerm (proj₁ ([F₊] ⊢Δ [σ])) [σs≡σ′s] [σ′s≡σ′s′]
      appEq = convEqTerm₂ [σFₙ] [σFₛₙ′]′ [Fₙ≡Fₛₙ′]′
                (app-congTerm [σFₙ′] [σFₛₙ′]′ [σF₊ₙ′]
                  (app-congTerm [σℕ] [σF₊ₙ′] (proj₁ ([F₊] ⊢Δ [σ])) [σs≡σ′s′]
                                [n′] [m′] [n′≡m′])
                  (natrec2Term {F} { ! } {lF} {z} {s} {n′} {σ = σ} rFlF
                              [Γ] [F] [F₀] [F₊] [z] [s] ⊢Δ [σ] [n′])
                  (convTerm₂ [σFₙ′] [σ′F′ₘ′] [σFₙ′≡σ′F′ₘ′]
                             (natrec2Term {F′} { ! } {lF} {z′} {s′} {m′} {σ = σ′} rFlF
                                         [Γ] [F′] [F′₀] [F′₊] [z′] [s′]
                                         ⊢Δ [σ′] [m′]))
                  (natrec2-congTerm {F} {F′} { ! } {lF} {z} {z′} {s} {s′} {n′} {m′} {σ = σ} rFlF
                                   [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀]
                                   [F₊] [F′₊] [F₊≡F′₊] [z] [z′] [z≡z′]
                                   [s] [s′] [s≡s′]
                                   ⊢Δ [σ] [σ′] [σ≡σ′] [n′] [m′] [n′≡m′]))
      reduction₁ = natrec2-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σsn′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , ι lF ])
                                  (PE.sym (singleSubstComp t σ F))
                                  (PE.sym (singleSubstComp t′ σ F))
                                  (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
                   ⇨∷* (conv* (natrec2-suc ⊢n′ ⊢F ⊢z ⊢s
                   ⇨   id (escapeTerm [σFₛₙ′] natrecN′))
                          (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡Fₛₙ′]))))
      reduction₂ = natrec2-subst* ⊢F′ ⊢z′ ⊢s′ (redₜ d′) [σ′ℕ2] [σ′sm′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , ι lF ])
                                  (PE.sym (singleSubstComp t σ′ F′))
                                  (PE.sym (singleSubstComp t′ σ′ F′))
                                  (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                               (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                      ([σ′] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
                   ⇨∷* (conv* (natrec2-suc ⊢m′ ⊢F′ ⊢z′ ⊢s′
                   ⇨   id (escapeTerm [σ′F′ₛₘ′] natrecM′))
                          (sym (≅-eq (escapeEq [σ′F′ₘ] [F′ₘ≡F′ₛₘ′]))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σFₛₙ′]
                                            [Fₙ≡Fₛₙ′] natrecN′))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] [σ′F′ₛₘ′]
                                            [F′ₘ≡F′ₛₘ′] natrecM′))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] appEq
                               (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ]
                                            (symEqTerm [σ′F′ₘ] eq₂)))
natrec2-congTerm {F} {F′} {rF = %} {lF} {z} {z′} {s} {s′} {n} {m} {Γ} {Δ} {σ} {σ′} {l} rFlF
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ .(suc2 n′) d n≡n (suc2ᵣ {n′} [n′]))
                (ℕ2ₜ .(suc2 m′) d′ m≡m (suc2ᵣ {m′} [m′]))
                (ℕ2ₜ₌ .(suc2 n″) .(suc2 m″) d₁ d₁′
                     t≡u (suc2ᵣ {n″} {m″} [n″≡m″])) =
  let n″≡n′ = suc2-PE-injectivity (whrDet*Term (redₜ d₁ , suc2ₙ) (redₜ d , suc2ₙ))
      m″≡m′ = suc2-PE-injectivity (whrDet*Term (redₜ d₁′ , suc2ₙ) (redₜ d′ , suc2ₙ))
      [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      [σ′ℕ2] = proj₁ ([ℕ2] ⊢Δ [σ′])
      [n′≡m′] = irrelevanceEqTerm″ PE.refl PE.refl n″≡n′ m″≡m′ PE.refl [σℕ] [σℕ] [n″≡m″]
      [σn] = ℕ2ₜ (suc2 n′) d n≡n (suc2ᵣ [n′])
      [σ′m] = ℕ2ₜ (suc2 m′) d′ m≡m (suc2ᵣ [m′])
      [σn≡σ′m] = ℕ2ₜ₌ (suc2 n″) (suc2 m″) d₁ d₁′ t≡u (suc2ᵣ [n″≡m″])
      ⊢ℕ2 = escape [σℕ]
      ⊢F = escape (proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢n′ = escapeTerm {l = l} [σℕ] [n′]
      ⊢ℕ2′ = escape [σ′ℕ2]
      ⊢F′ = escape (proj₁ ([F′] (⊢Δ ∙ ⊢ℕ2′)
                      (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′])))
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F′ zero2)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                    (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ′ F′ % lF)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′]))
                                    (proj₁ ([s′] ⊢Δ [σ′])))
      ⊢m′ = escapeTerm {l = l} [σ′ℕ2] [m′]
      [σsn′] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σℕ]
                               (ℕ2ₜ (suc2 n′) (idRedTerm:*: (suc2ⱼ ⊢n′)) n≡n (suc2ᵣ [n′]))
      [σn]′ , [σn≡σsn′] = redSubst*Term (redₜ d) [σℕ] [σsn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₛₙ′] = irrelevance′ (PE.sym (singleSubstComp (suc2 n′) σ F))
                             (proj₁ ([F] ⊢Δ ([σ] , [σsn′])))
      [Fₙ≡Fₛₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.sym (singleSubstComp (suc2 n′) σ F)) PE.refl PE.refl 
                                  [σFₙ]′ [σFₙ]
                                  (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                         (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [Fₙ≡Fₛₙ′]′ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (natrec2IrrelevantSubst {lF} F z s n′ σ) PE.refl PE.refl 
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σsn′])
                                          (reflSubst [Γ] ⊢Δ [σ] , [σn≡σsn′]))
      [σFₙ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                              (substSingletonComp F)))
                            (proj₁ ([F] ⊢Δ ([σ] , [n′])))
      [σFₛₙ′]′ = irrelevance′ (natrec2IrrelevantSubst {lF} F z s n′ σ)
                              (proj₁ ([F] ⊢Δ ([σ] , [σsn′])))
      [σ′sm′] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) [σ′ℕ2]
                                (ℕ2ₜ (suc2 m′) (idRedTerm:*: (suc2ⱼ ⊢m′)) m≡m (suc2ᵣ [m′]))
      [σ′m]′ , [σ′m≡σ′sm′] = redSubst*Term (redₜ d′) [σ′ℕ2] [σ′sm′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₛₘ′] = irrelevance′ (PE.sym (singleSubstComp (suc2 m′) σ′ F′))
                               (proj₁ ([F′] ⊢Δ ([σ′] , [σ′sm′])))
      [F′ₘ≡F′ₛₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                    (PE.sym (singleSubstComp (suc2 m′) σ′ F′)) PE.refl PE.refl 
                                    [σ′F′ₘ]′ [σ′F′ₘ]
                                    (proj₂ ([F′] ⊢Δ ([σ′] , [σ′m]))
                                           ([σ′] , [σ′sm′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′sm′]))
      [σ′Fₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F)
                                               (substSingletonComp F)))
                             (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₘ′] = irrelevance′ (PE.sym (PE.trans (substCompEq F′)
                                                (substSingletonComp F′)))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [m′])))
      [σ′F′ₛₘ′]′ = irrelevance′ (natrec2IrrelevantSubst {lF} F′ z′ s′ m′ σ′)
                                (proj₁ ([F′] ⊢Δ ([σ′] , [σ′sm′])))
      [σFₙ′≡σ′Fₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp n′ σ F))
                                     (PE.sym (singleSubstComp m′ σ′ F)) PE.refl PE.refl
                                     (proj₁ ([F] ⊢Δ ([σ] , [n′]))) [σFₙ′]
                                     (proj₂ ([F] ⊢Δ ([σ] , [n′]))
                                            ([σ′] , [m′]) ([σ≡σ′] , [n′≡m′]))
      [σ′Fₘ′≡σ′F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m′ σ′ F))
                                       (PE.sym (singleSubstComp m′ σ′ F′)) PE.refl PE.refl
                                       (proj₁ ([F] ⊢Δ ([σ′] , [m′])))
                                       [σ′Fₘ′] ([F≡F′] ⊢Δ ([σ′] , [m′]))
      [σFₙ′≡σ′F′ₘ′] = transEq [σFₙ′] [σ′Fₘ′] [σ′F′ₘ′] [σFₙ′≡σ′Fₘ′] [σ′Fₘ′≡σ′F′ₘ′]
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F)) PE.refl PE.refl
                                   (proj₁ ([F] ⊢Δ ([σ] , [σn]))) [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn]))
                                          ([σ′] , [σ′m]) ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′)) PE.refl PE.refl
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [[ ⊢n , _ , _ ]] = d
      [[ ⊢n′ , _ , _ ]] = d′
  in logRelIrrEq [σFₙ] (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n) (conv (natrec2ⱼ rFlF ⊢F′ ⊢z′ ⊢s′ ⊢n′) (sym (≅-eq (escapeEq  [σFₙ] [σFₙ≡σ′F′ₘ]))))

natrec2-congTerm {F} {F′} {rF = !} {lF} {z} {z′} {s} {s′} {n} {m} {Γ} {Δ} {σ} {σ′} {l} rFlF
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ .zero2 d n≡n zero2ᵣ) (ℕ2ₜ .zero2 d₁ m≡m zero2ᵣ)
                (ℕ2ₜ₌ .zero2 .zero2 d₂ d′ t≡u zero2ᵣ) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      ⊢F = escape (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ2)
                                 (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢F′ = escape (proj₁ ([F′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢ℕ2)
                                   (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′])))
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F′ zero2)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ′ F′ ! lF)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′])) (proj₁ ([s′] ⊢Δ [σ′])))
      [σ0] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) (proj₁ ([ℕ2] ⊢Δ [σ]))
                             (ℕ2ₜ zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) n≡n zero2ᵣ)
      [σ′0] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) (proj₁ ([ℕ2] ⊢Δ [σ′]))
                              (ℕ2ₜ zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) m≡m zero2ᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ2] ⊢Δ [σ])) [σ0]
      [σ′m]′ , [σ′m≡σ′0] = redSubst*Term (redₜ d′) (proj₁ ([ℕ2] ⊢Δ [σ′])) [σ′0]
      [σn] = ℕ2ₜ zero2 d n≡n zero2ᵣ
      [σ′m] = ℕ2ₜ zero2 d′ m≡m zero2ᵣ
      [σn≡σ′m] = ℕ2ₜ₌ zero2 zero2 d₂ d′ t≡u zero2ᵣ
      [σn≡σ′0] = transEqTerm [σℕ] [σn≡σ′m] [σ′m≡σ′0]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F)) PE.refl PE.refl 
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′)) PE.refl PE.refl 
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [Fₙ≡F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ] , [σ0]) (reflSubst [Γ] ⊢Δ [σ] , [σn≡σ0])
      [Fₙ≡F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F)) PE.refl PE.refl 
                                [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [σFₙ≡σ′F₀]′ = proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′0]) ([σ≡σ′] , [σn≡σ′0])
      [σFₙ≡σ′F₀] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (substCompEq F)) PE.refl PE.refl 
                                [σFₙ]′ [σFₙ] [σFₙ≡σ′F₀]′
      [F′ₘ≡F′₀]′ = proj₂ ([F′] ⊢Δ ([σ′] , [σ′m])) ([σ′] , [σ′0])
                         (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′0])
      [F′ₘ≡F′₀] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                  (PE.sym (substCompEq F′)) PE.refl PE.refl 
                                  [σ′F′ₘ]′ [σ′F′ₘ] [F′ₘ≡F′₀]′
      [Fₙ≡F₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                  (PE.trans (substConcatSingleton′ F)
                                            (PE.sym (singleSubstComp zero2 σ F))) PE.refl PE.refl 
                                  [σFₙ]′ [σFₙ] [Fₙ≡F₀]′
      [F′ₘ≡F′₀]″ = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                    (PE.trans (substConcatSingleton′ F′)
                                              (PE.sym (singleSubstComp zero2 σ′ F′))) PE.refl PE.refl 
                                    [σ′F′ₘ]′ [σ′F′ₘ] [F′ₘ≡F′₀]′
      [σz] = proj₁ ([z] ⊢Δ [σ])
      [σ′z′] = proj₁ ([z′] ⊢Δ [σ′])
      [σz≡σ′z] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ])) [Fₙ≡F₀]
                             (proj₂ ([z] ⊢Δ [σ]) [σ′] [σ≡σ′])
      [σ′z≡σ′z′] = convEqTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ′])) [σFₙ≡σ′F₀]
                               ([z≡z′] ⊢Δ [σ′])
      [σz≡σ′z′] = transEqTerm [σFₙ] [σz≡σ′z] [σ′z≡σ′z′]
      reduction₁ = natrec2-subst* ⊢F ⊢z ⊢s (redₜ d) (proj₁ ([ℕ2] ⊢Δ [σ])) [σ0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , ι lF ])
                                 (PE.sym (singleSubstComp t σ F))
                                 (PE.sym (singleSubstComp t′ σ F))
                                 (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                              (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                     ([σ] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
                  ⇨∷* (conv* (natrec2-zero ⊢F ⊢z ⊢s ⇨ id ⊢z)
                             (sym (≅-eq (escapeEq [σFₙ] [Fₙ≡F₀]″))))
      reduction₂ = natrec2-subst* ⊢F′ ⊢z′ ⊢s′ (redₜ d′) (proj₁ ([ℕ2] ⊢Δ [σ′])) [σ′0]
                    (λ {t} {t′} [t] [t′] [t≡t′] →
                       PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , ι lF ])
                                 (PE.sym (singleSubstComp t σ′ F′))
                                 (PE.sym (singleSubstComp t′ σ′ F′))
                                 (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                              (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                     ([σ′] , [t′])
                                                     (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
                  ⇨∷* (conv* (natrec2-zero ⊢F′ ⊢z′ ⊢s′ ⇨ id ⊢z′)
                             (sym (≅-eq (escapeEq [σ′F′ₘ] [F′ₘ≡F′₀]″))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] (proj₁ ([F₀] ⊢Δ [σ]))
                                            [Fₙ≡F₀] [σz]))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] (proj₁ ([F′₀] ⊢Δ [σ′]))
                                            [F′ₘ≡F′₀] [σ′z′]))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] [σz≡σ′z′]
                               (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ]
                                            (symEqTerm [σ′F′ₘ] eq₂)))
natrec2-congTerm {F} {F′} {rF = %} {lF} {z} {z′} {s} {s′} {n} {m} {Γ} {Δ} {σ} {σ′} {l} rFlF
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ .zero2 d n≡n zero2ᵣ) (ℕ2ₜ .zero2 d₁ m≡m zero2ᵣ)
                (ℕ2ₜ₌ .zero2 .zero2 d₂ d′ t≡u zero2ᵣ) =
  let [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      ⊢F = escape (proj₁ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ2)
                                 (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ])))
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢F′ = escape (proj₁ ([F′] {σ = liftSubst σ′} (⊢Δ ∙ ⊢ℕ2)
                                   (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′])))
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F′ zero2)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ′ F′ % lF)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′])) (proj₁ ([s′] ⊢Δ [σ′])))
      [σ0] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) (proj₁ ([ℕ2] ⊢Δ [σ]))
                             (ℕ2ₜ zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) n≡n zero2ᵣ)
      [σ′0] = irrelevanceTerm {l = l} (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) (proj₁ ([ℕ2] ⊢Δ [σ′]))
                              (ℕ2ₜ zero2 (idRedTerm:*: (zero2ⱼ ⊢Δ)) m≡m zero2ᵣ)
      [σn]′ , [σn≡σ0] = redSubst*Term (redₜ d) (proj₁ ([ℕ2] ⊢Δ [σ])) [σ0]
      [σ′m]′ , [σ′m≡σ′0] = redSubst*Term (redₜ d′) (proj₁ ([ℕ2] ⊢Δ [σ′])) [σ′0]
      [σn] = ℕ2ₜ zero2 d n≡n zero2ᵣ
      [σ′m] = ℕ2ₜ zero2 d′ m≡m zero2ᵣ
      [σn≡σ′m] = ℕ2ₜ₌ zero2 zero2 d₂ d′ t≡u zero2ᵣ
      [σn≡σ′0] = transEqTerm [σℕ] [σn≡σ′m] [σ′m≡σ′0]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F)) PE.refl PE.refl
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′)) PE.refl PE.refl
                                     [σ′Fₘ]′ [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [[ ⊢n , _ , _ ]] = d
      [[ ⊢n′ , _ , _ ]] = d₁
  in logRelIrrEq [σFₙ] (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n) (conv (natrec2ⱼ rFlF ⊢F′ ⊢z′ ⊢s′ ⊢n′) (sym (≅-eq (escapeEq  [σFₙ] [σFₙ≡σ′F′ₘ]))))


natrec2-congTerm {F} {F′} {rF = !} {lF} {z} {z′} {s} {s′} {n} {m} {Γ} {Δ} {σ} {σ′} {l} rFlF
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁)))
                (ℕ2ₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁)))
                (ℕ2ₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))) =
  let n″≡n′ = whrDet*Term (redₜ d₁ , ne x₂) (redₜ d , ne neN′)
      m″≡m′ = whrDet*Term (redₜ d₁′ , ne x₃) (redₜ d′ , ne neM′)
      [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      [σ′ℕ2] = proj₁ ([ℕ2] ⊢Δ [σ′])
      [σn] = ℕ2ₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁))
      [σ′m] = ℕ2ₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁))
      [σn≡σ′m] = ℕ2ₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      [σ′F] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′]))
      [σ′F′] = proj₁ ([F′] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′]))
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F zero2)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢s≡s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ s ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ F ! lF)
                      (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₁ ([s] ⊢Δ [σ]))))
      ⊢F′ = escape [σ′F′]
      ⊢F′≡F′ = escapeEq [σ′F′] (reflEq [σ′F′])
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F′ zero2)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢z′≡z′ = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F′ zero2)
                        (escapeTermEq (proj₁ ([F′₀] ⊢Δ [σ′]))
                                          (reflEqTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                                      (proj₁ ([z′] ⊢Δ [σ′]))))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ′ F′ ! lF)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′])) (proj₁ ([s′] ⊢Δ [σ′])))
      ⊢s′≡s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ≅ subst σ′ s′ ∷ x ^ [ ! , ι lF ]) (natrec2SucCase σ′ F′ ! lF)
                      (escapeTermEq (proj₁ ([F′₊] ⊢Δ [σ′]))
                                        (reflEqTerm (proj₁ ([F′₊] ⊢Δ [σ′]))
                                                    (proj₁ ([s′] ⊢Δ [σ′]))))
      ⊢σF≡σ′F = escapeEq [σF] (proj₂ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ2)
                                           (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
                                      {σ′ = liftSubst σ′}
                                      (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′])
                                      (liftSubstSEq {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ] [σ≡σ′]))
      ⊢σz≡σ′z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ ! , ι lF ]) (singleSubstLift F zero2)
                         (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                          (proj₂ ([z] ⊢Δ [σ]) [σ′] [σ≡σ′]))
      ⊢σs≡σ′s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ′ s ∷ x ^ [ ! , ι lF ])
                         (natrec2SucCase σ F ! lF)
                         (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                          (proj₂ ([s] ⊢Δ [σ]) [σ′] [σ≡σ′]))
      ⊢σ′F≡⊢σ′F′ = escapeEq [σ′F] ([F≡F′] (⊢Δ ∙ ⊢ℕ2)
                               (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′]))
      ⊢σ′z≡⊢σ′z′ = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ ! , ι lF ])
                            (singleSubstLift F zero2)
                            (≅-conv (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ′]))
                                                   ([z≡z′] ⊢Δ [σ′]))
                                  (sym (≅-eq (escapeEq (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₂ ([F₀] ⊢Δ [σ]) [σ′] [σ≡σ′])))))
      ⊢σ′s≡⊢σ′s′ = PE.subst (λ x → Δ ⊢ subst σ′ s ≅ subst σ′ s′ ∷ x ^ [ ! , ι lF ])
                            (natrec2SucCase σ F ! lF)
                            (≅-conv (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ′]))
                                                   ([s≡s′] ⊢Δ [σ′]))
                                  (sym (≅-eq (escapeEq (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₂ ([F₊] ⊢Δ [σ]) [σ′] [σ≡σ′])))))
      ⊢F≡F′ = ≅-trans ⊢σF≡σ′F ⊢σ′F≡⊢σ′F′
      ⊢z≡z′ = ≅ₜ-trans ⊢σz≡σ′z ⊢σ′z≡⊢σ′z′
      ⊢s≡s′ = ≅ₜ-trans ⊢σs≡σ′s ⊢σ′s≡⊢σ′s′
      [σn′] = neuTerm [σℕ] neN′ ⊢n′ n≡n₁
      [σn]′ , [σn≡σn′] = redSubst*Term (redₜ d) [σℕ] [σn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₙ′] = irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σn′])))
      [Fₙ≡Fₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (singleSubstComp n′ σ F)) PE.refl PE.refl [σFₙ]′ [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn])))
                                        ([σ] , [σn′])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σn′]))
      [σ′m′] = neuTerm [σ′ℕ2] neM′ ⊢m′ m≡m₁
      [σ′m]′ , [σ′m≡σ′m′] = redSubst*Term (redₜ d′) [σ′ℕ2] [σ′m′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ′] = irrelevance′ (PE.sym (singleSubstComp m′ σ′ F′))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [σ′m′])))
      [F′ₘ≡F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                   (PE.sym (singleSubstComp m′ σ′ F′)) PE.refl PE.refl
                                   [σ′F′ₘ]′ [σ′F′ₘ]
                                   ((proj₂ ([F′] ⊢Δ ([σ′] , [σ′m])))
                                           ([σ′] , [σ′m′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′m′]))
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F)) PE.refl PE.refl
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′)) PE.refl PE.refl
                                     (proj₁ ([F] ⊢Δ ([σ′] , [σ′m])))
                                     [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [σFₙ′≡σ′Fₘ′] = transEq [σFₙ′] [σFₙ] [σ′F′ₘ′] (symEq [σFₙ] [σFₙ′] [Fₙ≡Fₙ′])
                             (transEq [σFₙ] [σ′F′ₘ] [σ′F′ₘ′] [σFₙ≡σ′F′ₘ] [F′ₘ≡F′ₘ′])
      natrecN = neuTerm [σFₙ′] (natrec2ₙ neN′) (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n′)
                        (~-natrec2 ⊢F≡F ⊢z≡z ⊢s≡s n≡n₁)
      natrecM = neuTerm [σ′F′ₘ′] (natrec2ₙ neM′) (natrec2ⱼ rFlF ⊢F′ ⊢z′ ⊢s′ ⊢m′)
                        (~-natrec2 ⊢F′≡F′ ⊢z′≡z′ ⊢s′≡s′ m≡m₁)
      natrecN≡M =
        convEqTerm₂ [σFₙ] [σFₙ′] [Fₙ≡Fₙ′]
          (neuEqTerm [σFₙ′] (natrec2ₙ neN′) (natrec2ₙ neM′)
                     (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n′)
                     (conv (natrec2ⱼ rFlF ⊢F′ ⊢z′ ⊢s′ ⊢m′)
                            (sym (≅-eq (escapeEq [σFₙ′] [σFₙ′≡σ′Fₘ′]))))
                     (~-natrec2 ⊢F≡F′ ⊢z≡z′ ⊢s≡s′
                               (PE.subst₂ (λ x y → _ ⊢ x ~ y ∷ _ ^ [ ! , ι ⁰ ])
                                          n″≡n′ m″≡m′ prop₂)))
      reduction₁ = natrec2-subst* ⊢F ⊢z ⊢s (redₜ d) [σℕ] [σn′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , ι lF ])
                                  (PE.sym (singleSubstComp t σ F))
                                  (PE.sym (singleSubstComp t′ σ F))
                                  (≅-eq (escapeEq (proj₁ ([F] ⊢Δ ([σ] , [t])))
                                               (proj₂ ([F] ⊢Δ ([σ] , [t]))
                                                      ([σ] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ] , [t≡t′])))))
      reduction₂ = natrec2-subst* ⊢F′ ⊢z′ ⊢s′ (redₜ d′) [σ′ℕ2] [σ′m′]
                     (λ {t} {t′} [t] [t′] [t≡t′] →
                        PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ [ ! , ι lF ])
                                  (PE.sym (singleSubstComp t σ′ F′))
                                  (PE.sym (singleSubstComp t′ σ′ F′))
                                  (≅-eq (escapeEq (proj₁ ([F′] ⊢Δ ([σ′] , [t])))
                                               (proj₂ ([F′] ⊢Δ ([σ′] , [t]))
                                                      ([σ′] , [t′])
                                                      (reflSubst [Γ] ⊢Δ [σ′] , [t≡t′])))))
      eq₁ = proj₂ (redSubst*Term reduction₁ [σFₙ]
                                 (convTerm₂ [σFₙ] [σFₙ′] [Fₙ≡Fₙ′] natrecN))
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′ₘ]
                                 (convTerm₂ [σ′F′ₘ] [σ′F′ₘ′] [F′ₘ≡F′ₘ′] natrecM))
  in  transEqTerm [σFₙ] eq₁
                  (transEqTerm [σFₙ] natrecN≡M
                               (convEqTerm₂ [σFₙ] [σ′F′ₘ] [σFₙ≡σ′F′ₘ]
                                            (symEqTerm [σ′F′ₘ] eq₂)))
                                            
natrec2-congTerm {F} {F′} {rF = %} {lF} {z} {z′} {s} {s′} {n} {m} {Γ} {Δ} {σ} {σ′} {l} rFlF 
                [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁)))
                (ℕ2ₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁)))
                  (ℕ2ₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))) =
  let n″≡n′ = whrDet*Term (redₜ d₁ , ne x₂) (redₜ d , ne neN′)
      m″≡m′ = whrDet*Term (redₜ d₁′ , ne x₃) (redₜ d′ , ne neM′)
      [ℕ2] = ℕ2ᵛ {l = l} [Γ]
      [σℕ] = proj₁ ([ℕ2] ⊢Δ [σ])
      [σ′ℕ2] = proj₁ ([ℕ2] ⊢Δ [σ′])
      [σn] = ℕ2ₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁))
      [σ′m] = ℕ2ₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁))
      [σn≡σ′m] = ℕ2ₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))
      ⊢ℕ2 = escape (proj₁ ([ℕ2] ⊢Δ [σ]))
      [σF] = proj₁ ([F] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
      [σ′F′] = proj₁ ([F′] (⊢Δ ∙ ⊢ℕ2) (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′]))
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢z = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F zero2)
                    (escapeTerm (proj₁ ([F₀] ⊢Δ [σ])) (proj₁ ([z] ⊢Δ [σ])))
      ⊢z≡z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F zero2)
                      (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                    (proj₁ ([z] ⊢Δ [σ]))))
      ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                    (escapeTerm (proj₁ ([F₊] ⊢Δ [σ])) (proj₁ ([s] ⊢Δ [σ])))
      ⊢s≡s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ s ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ F % lF)
                      (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                        (reflEqTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                    (proj₁ ([s] ⊢Δ [σ]))))
      ⊢F′ = escape [σ′F′]
      ⊢F′≡F′ = escapeEq [σ′F′] (reflEq [σ′F′])
      ⊢z′ = PE.subst (λ x → _ ⊢ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F′ zero2)
                     (escapeTerm (proj₁ ([F′₀] ⊢Δ [σ′])) (proj₁ ([z′] ⊢Δ [σ′])))
      ⊢z′≡z′ = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ % , ι lF ]) (singleSubstLift F′ zero2)
                        (escapeTermEq (proj₁ ([F′₀] ⊢Δ [σ′]))
                                          (reflEqTerm (proj₁ ([F′₀] ⊢Δ [σ′]))
                                                      (proj₁ ([z′] ⊢Δ [σ′]))))
      ⊢s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ′ F′ % lF)
                     (escapeTerm (proj₁ ([F′₊] ⊢Δ [σ′])) (proj₁ ([s′] ⊢Δ [σ′])))
      ⊢s′≡s′ = PE.subst (λ x → Δ ⊢ subst σ′ s′ ≅ subst σ′ s′ ∷ x ^ [ % , ι lF ]) (natrec2SucCase σ′ F′ % lF)
                      (escapeTermEq (proj₁ ([F′₊] ⊢Δ [σ′]))
                                        (reflEqTerm (proj₁ ([F′₊] ⊢Δ [σ′]))
                                                    (proj₁ ([s′] ⊢Δ [σ′]))))
      ⊢σF≡σ′F = escapeEq [σF] (proj₂ ([F] {σ = liftSubst σ} (⊢Δ ∙ ⊢ℕ2)
                                           (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ]))
                                      {σ′ = liftSubst σ′}
                                      (liftSubstS {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ′])
                                      (liftSubstSEq {F = ℕ2} [Γ] ⊢Δ [ℕ2] [σ] [σ≡σ′]))
      ⊢σz≡σ′z = PE.subst (λ x → _ ⊢ _ ≅ _ ∷ x ^ [ % , _ ]) (singleSubstLift F zero2)
                         (escapeTermEq (proj₁ ([F₀] ⊢Δ [σ]))
                                          (proj₂ ([z] ⊢Δ [σ]) [σ′] [σ≡σ′]))
      ⊢σs≡σ′s = PE.subst (λ x → Δ ⊢ subst σ s ≅ subst σ′ s ∷ x ^ [ % , ι lF ])
                         (natrec2SucCase σ F % lF)
                         (escapeTermEq (proj₁ ([F₊] ⊢Δ [σ]))
                                          (proj₂ ([s] ⊢Δ [σ]) [σ′] [σ≡σ′]))
      [σn′] = neuTerm [σℕ] neN′ ⊢n′ n≡n₁
      [σn]′ , [σn≡σn′] = redSubst*Term (redₜ d) [σℕ] [σn′]
      [σFₙ]′ = proj₁ ([F] ⊢Δ ([σ] , [σn]))
      [σFₙ] = irrelevance′ (PE.sym (singleSubstComp n σ F)) [σFₙ]′
      [σFₙ′] = irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                            (proj₁ ([F] ⊢Δ ([σ] , [σn′])))
      [Fₙ≡Fₙ′] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                (PE.sym (singleSubstComp n′ σ F)) PE.refl PE.refl [σFₙ]′ [σFₙ]
                                ((proj₂ ([F] ⊢Δ ([σ] , [σn])))
                                        ([σ] , [σn′])
                                        (reflSubst [Γ] ⊢Δ [σ] , [σn≡σn′]))
      [σ′m′] = neuTerm [σ′ℕ2] neM′ ⊢m′ m≡m₁
      [σ′m]′ , [σ′m≡σ′m′] = redSubst*Term (redₜ d′) [σ′ℕ2] [σ′m′]
      [σ′F′ₘ]′ = proj₁ ([F′] ⊢Δ ([σ′] , [σ′m]))
      [σ′F′ₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F′)) [σ′F′ₘ]′
      [σ′Fₘ]′ = proj₁ ([F] ⊢Δ ([σ′] , [σ′m]))
      [σ′Fₘ] = irrelevance′ (PE.sym (singleSubstComp m σ′ F)) [σ′Fₘ]′
      [σ′F′ₘ′] = irrelevance′ (PE.sym (singleSubstComp m′ σ′ F′))
                              (proj₁ ([F′] ⊢Δ ([σ′] , [σ′m′])))
      [F′ₘ≡F′ₘ′] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F′))
                                   (PE.sym (singleSubstComp m′ σ′ F′))  PE.refl PE.refl
                                   [σ′F′ₘ]′ [σ′F′ₘ]
                                   ((proj₂ ([F′] ⊢Δ ([σ′] , [σ′m])))
                                           ([σ′] , [σ′m′])
                                           (reflSubst [Γ] ⊢Δ [σ′] , [σ′m≡σ′m′]))
      [σFₙ≡σ′Fₘ] = irrelevanceEq″ (PE.sym (singleSubstComp n σ F))
                                   (PE.sym (singleSubstComp m σ′ F)) PE.refl PE.refl
                                   [σFₙ]′ [σFₙ]
                                   (proj₂ ([F] ⊢Δ ([σ] , [σn])) ([σ′] , [σ′m])
                                          ([σ≡σ′] , [σn≡σ′m]))
      [σ′Fₘ≡σ′F′ₘ] = irrelevanceEq″ (PE.sym (singleSubstComp m σ′ F))
                                     (PE.sym (singleSubstComp m σ′ F′)) PE.refl PE.refl
                                     (proj₁ ([F] ⊢Δ ([σ′] , [σ′m])))
                                     [σ′Fₘ] ([F≡F′] ⊢Δ ([σ′] , [σ′m]))
      [σFₙ≡σ′F′ₘ] = transEq [σFₙ] [σ′Fₘ] [σ′F′ₘ] [σFₙ≡σ′Fₘ] [σ′Fₘ≡σ′F′ₘ]
      [[ ⊢n , _ , _ ]] = d
      [[ ⊢n′ , _ , _ ]] = d′
  in logRelIrrEq [σFₙ] (natrec2ⱼ rFlF ⊢F ⊢z ⊢s ⊢n)  (conv (natrec2ⱼ rFlF ⊢F′ ⊢z′ ⊢s′ ⊢n′) (sym (≅-eq (escapeEq  [σFₙ] [σFₙ≡σ′F′ₘ]))))

-- Refuting cases
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕ2ₜ _ d₁ _ zero2ᵣ)
                (ℕ2ₜ₌ _ _ d₂ d′ t≡u (suc2ᵣ prop₂)) =
  ⊥-elim (zero2≢suc2 (whrDet*Term (redₜ d₁ , zero2ₙ) (redₜ d′ , suc2ₙ)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕ2ₜ n d₁ _ (ne (neNfₜ neK ⊢k k≡k)))
                (ℕ2ₜ₌ _ _ d₂ d′ t≡u (suc2ᵣ prop₂)) =
  ⊥-elim (suc2≢ne neK (whrDet*Term (redₜ d′ , suc2ₙ) (redₜ d₁ , ne neK)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ _ d _ zero2ᵣ) [σm]
                (ℕ2ₜ₌ _ _ d₁ d′ t≡u (suc2ᵣ prop₂)) =
  ⊥-elim (zero2≢suc2 (whrDet*Term (redₜ d , zero2ₙ) (redₜ d₁ , suc2ₙ)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ n d _ (ne (neNfₜ neK ⊢k k≡k))) [σm]
                (ℕ2ₜ₌ _ _ d₁ d′ t≡u (suc2ᵣ prop₂)) =
  ⊥-elim (suc2≢ne neK (whrDet*Term (redₜ d₁ , suc2ₙ) (redₜ d , ne neK)))

natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ _ d _ (suc2ᵣ prop)) [σm]
                (ℕ2ₜ₌ _ _ d₂ d′ t≡u zero2ᵣ) =
  ⊥-elim (zero2≢suc2 (whrDet*Term (redₜ d₂ , zero2ₙ) (redₜ d , suc2ₙ)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕ2ₜ _ d₁ _ (suc2ᵣ prop₁))
                (ℕ2ₜ₌ _ _ d₂ d′ t≡u zero2ᵣ) =
  ⊥-elim (zero2≢suc2 (whrDet*Term (redₜ d′ , zero2ₙ) (redₜ d₁ , suc2ₙ)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕ2ₜ n d₁ _ (ne (neNfₜ neK ⊢k k≡k)))
                (ℕ2ₜ₌ _ _ d₂ d′ t≡u zero2ᵣ) =
  ⊥-elim (zero2≢ne neK (whrDet*Term (redₜ d′ , zero2ₙ) (redₜ d₁ , ne neK)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ n d _ (ne (neNfₜ neK ⊢k k≡k))) [σm]
                (ℕ2ₜ₌ _ _ d₂ d′ t≡u zero2ᵣ) =
  ⊥-elim (zero2≢ne neK (whrDet*Term (redₜ d₂ , zero2ₙ) (redₜ d , ne neK)))

natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ _ d _ (suc2ᵣ prop)) [σm]
                (ℕ2ₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x x₁ prop₂))) =
  ⊥-elim (suc2≢ne x (whrDet*Term (redₜ d , suc2ₙ) (redₜ d₂ , ne x)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                (ℕ2ₜ _ d _ zero2ᵣ) [σm]
                (ℕ2ₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x x₁ prop₂))) =
  ⊥-elim (zero2≢ne x (whrDet*Term (redₜ d , zero2ₙ) (redₜ d₂ , ne x)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕ2ₜ _ d₁ _ (suc2ᵣ prop₁))
                (ℕ2ₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x₁ x₂ prop₂))) =
  ⊥-elim (suc2≢ne x₂ (whrDet*Term (redₜ d₁ , suc2ₙ) (redₜ d′ , ne x₂)))
natrec2-congTerm rFlF [Γ] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
                [z] [z′] [z≡z′] [s] [s′] [s≡s′] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σn] (ℕ2ₜ _ d₁ _ zero2ᵣ)
                (ℕ2ₜ₌ n₁ n′ d₂ d′ t≡u (ne (neNfₜ₌ x₁ x₂ prop₂))) =
  ⊥-elim (zero2≢ne x₂ (whrDet*Term (redₜ d₁ , zero2ₙ) (redₜ d′ , ne x₂)))



-- Validity of natural2 recursion.
natrec2ᵛ : ∀ {F rF lF z s n Γ l}
          (rFlF : rF PE.≡ % → lF PE.≡ ⁰)
          ([Γ] : ⊩ᵛ Γ)
          ([ℕ2]  : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
          ([F]  : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2])
          ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero2 ] ^ [ rF , ι lF ] / [Γ])
          ([F₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF  ° lF ^ rF) ° lF  ° lF ^ rF ^ [ rF , ι lF ] / [Γ])
          ([Fₙ] : Γ ⊩ᵛ⟨ l ⟩ F [ n ] ^ [ rF , ι lF ] / [Γ])
        → Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero2 ]  ^ [ rF , ι lF ] / [Γ] / [F₀]
        → Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ] / [F₊]
        → ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] / [ℕ2])
        → Γ ⊩ᵛ⟨ l ⟩ natrec2 lF F z s n ∷ F [ n ] ^ [ rF , ι lF ] / [Γ] / [Fₙ]
natrec2ᵛ {F} {rF} {lF} {z} {s} {n} {l = l} rFlF  [Γ] [ℕ2] [F] [F₀] [F₊] [Fₙ] [z] [s] [n]
        {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]′ = S.irrelevance {A = F} (_∙_ {A = ℕ2} [Γ] [ℕ2])
                           (_∙_ {l = l} [Γ] (ℕ2ᵛ [Γ])) [F]
      [σn]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ2] ⊢Δ [σ]))
                              (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) (proj₁ ([n] ⊢Δ [σ]))
      n′ = subst σ n
      eqPrf = PE.trans (singleSubstComp n′ σ F)
                       (PE.sym (PE.trans (substCompEq F)
                               (substConcatSingleton′ F)))
  in  irrelevanceTerm′ eqPrf PE.refl PE.refl (irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                                           (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′))))
                        (proj₁ ([Fₙ] ⊢Δ [σ]))
                   (natrec2Term {F} {rF} {lF} {z} {s} {n′} {σ = σ} rFlF [Γ]
                               [F]′
                               [F₀] [F₊] [z] [s] ⊢Δ [σ]
                               [σn]′)
 ,   (λ {σ′} [σ′] [σ≡σ′] →
        let [σ′n]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ2] ⊢Δ [σ′]))
                                     (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ))))
                                     (proj₁ ([n] ⊢Δ [σ′]))
            [σn≡σ′n] = irrelevanceEqTerm {l′ = l} (proj₁ ([ℕ2] ⊢Δ [σ]))
                                         (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ))))
                                         (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])
        in  irrelevanceEqTerm′ eqPrf PE.refl PE.refl
              (irrelevance′ (PE.sym (singleSubstComp n′ σ F))
                            (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′))))
              (proj₁ ([Fₙ] ⊢Δ [σ]))
              (natrec2-congTerm {F} {F} {rF} {lF} {z} {z} {s} {s} {n′} {subst σ′ n} {σ = σ} rFlF 
                               [Γ] [F]′ [F]′ (reflᵛ {F} (_∙_ {A = ℕ2} {l = l}
                               [Γ] (ℕ2ᵛ [Γ])) [F]′) [F₀] [F₀]
                               (reflᵛ {F [ zero2 ]} [Γ] [F₀]) [F₊] [F₊]
                               (reflᵛ {Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF) ° lF ° lF ^ rF}
                                      [Γ] [F₊])
                               [z] [z] (reflᵗᵛ {F [ zero2 ]} {z} [Γ] [F₀] [z])
                               [s] [s]
                               (reflᵗᵛ {Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ) ° lF ° lF ^ rF} {s}
                                       [Γ] [F₊] [s])
                               ⊢Δ [σ] [σ′] [σ≡σ′] [σn]′ [σ′n]′ [σn≡σ′n]))

-- Validity of natural2 recursion congruence.
natrec2-congᵛ : ∀ {F F′ rF lF z z′ s s′ n n′ Γ l}
          (rFlF : rF PE.≡ % → lF PE.≡ ⁰)
          ([Γ] : ⊩ᵛ Γ)
          ([ℕ2]  : Γ ⊩ᵛ⟨ l ⟩ ℕ2 ^ [ ! , ι ⁰ ] / [Γ])
          ([F]  : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2])
          ([F′]  : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F′ ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2])
          ([F≡F′]  : Γ ∙ ℕ2 ^ [ ! , ι ⁰ ] ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ [ rF , ι lF ] / [Γ] ∙ [ℕ2] / [F])
          ([F₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero2 ] ^ [ rF , ι lF ] / [Γ])
          ([F′₀] : Γ ⊩ᵛ⟨ l ⟩ F′ [ zero2 ] ^ [ rF , ι lF ] / [Γ])
          ([F₀≡F′₀] : Γ ⊩ᵛ⟨ l ⟩ F [ zero2 ] ≡ F′ [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F₀])
          ([F₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ])
          ([F′₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F′ ^ rF ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF  ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ])
          ([F₊≡F′₊] : Γ ⊩ᵛ⟨ l ⟩ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ) ° lF ° lF ^ rF
                              ≡ Π ℕ2 ^ ! ° ⁰ ▹ (F′ ^ rF ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF  ° lF ^ rF) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ]
                              / [F₊])
          ([Fₙ] : Γ ⊩ᵛ⟨ l ⟩ F [ n ] ^ [ rF , ι lF ] / [Γ])
          ([z] : Γ ⊩ᵛ⟨ l ⟩ z ∷ F [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F₀])
          ([z′] : Γ ⊩ᵛ⟨ l ⟩ z′ ∷ F′ [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F′₀])
          ([z≡z′] : Γ ⊩ᵛ⟨ l ⟩ z ≡ z′ ∷ F [ zero2 ] ^ [ rF , ι lF ] / [Γ] / [F₀])
          ([s] : Γ ⊩ᵛ⟨ l ⟩ s ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ] / [F₊])
          ([s′] : Γ ⊩ᵛ⟨ l ⟩ s′ ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F′ ^ rF ° lF ▹▹ F′ [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ]
                           / [F′₊])
          ([s≡s′] : Γ ⊩ᵛ⟨ l ⟩ s ≡ s′ ∷ Π ℕ2 ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc2 (var 0) ]↑ ° lF ° lF ^ rF ) ° lF ° lF ^ rF ^ [ rF , ι lF ] / [Γ] / [F₊])
          ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] / [ℕ2])
          ([n′] : Γ ⊩ᵛ⟨ l ⟩ n′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] / [ℕ2])
          ([n≡n′] : Γ ⊩ᵛ⟨ l ⟩ n ≡ n′ ∷ ℕ2 ^ [ ! , ι ⁰ ] / [Γ] / [ℕ2])
        → Γ ⊩ᵛ⟨ l ⟩ natrec2 lF F z s n ≡ natrec2 lF F′ z′ s′ n′ ∷ F [ n ] ^ [ rF , ι lF ] / [Γ] / [Fₙ]
natrec2-congᵛ {F} {F′} {rF} {lF} {z} {z′} {s} {s′} {n} {n′} {l = l} rFlF
             [Γ] [ℕ2] [F] [F′] [F≡F′] [F₀] [F′₀] [F₀≡F′₀] [F₊] [F′₊] [F₊≡F′₊]
             [Fₙ] [z] [z′] [z≡z′] [s] [s′] [s≡s′] [n] [n′]
             [n≡n′] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]′ = S.irrelevance {A = F} (_∙_ {A = ℕ2} [Γ] [ℕ2])
                           (_∙_ {l = l} [Γ] (ℕ2ᵛ [Γ])) [F]
      [F′]′ = S.irrelevance {A = F′} (_∙_ {A = ℕ2} [Γ] [ℕ2])
                            (_∙_ {l = l} [Γ] (ℕ2ᵛ [Γ])) [F′]
      [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} (_∙_ {A = ℕ2} [Γ] [ℕ2])
                                (_∙_ {l = l} [Γ] (ℕ2ᵛ [Γ])) [F] [F]′ [F≡F′]
      [σn]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ2] ⊢Δ [σ]))
                              (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) (proj₁ ([n] ⊢Δ [σ]))
      [σn′]′ = irrelevanceTerm {l′ = l} (proj₁ ([ℕ2] ⊢Δ [σ]))
                               (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) (proj₁ ([n′] ⊢Δ [σ]))
      [σn≡σn′]′ = irrelevanceEqTerm {l′ = l} (proj₁ ([ℕ2] ⊢Δ [σ]))
                                    (ℕ2ᵣ (idRed:*: (univ (ℕ2ⱼ ⊢Δ)))) ([n≡n′] ⊢Δ [σ])
      [Fₙ]′ = irrelevance′ (PE.sym (singleSubstComp (subst σ n) σ F))
                           (proj₁ ([F]′ ⊢Δ ([σ] , [σn]′)))
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift F n)) PE.refl PE.refl 
                         [Fₙ]′ (proj₁ ([Fₙ] ⊢Δ [σ]))
                         (natrec2-congTerm {F} {F′} {rF} {lF} {z} {z′} {s} {s′} 
                                          {subst σ n} {subst σ n′} rFlF
                                          [Γ] [F]′ [F′]′ [F≡F′]′
                                          [F₀] [F′₀] [F₀≡F′₀]
                                          [F₊] [F′₊] [F₊≡F′₊]
                                          [z] [z′] [z≡z′]
                                          [s] [s′] [s≡s′] ⊢Δ
                                          [σ] [σ] (reflSubst [Γ] ⊢Δ [σ])
                                          [σn]′ [σn′]′ [σn≡σn′]′)

