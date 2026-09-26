import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.Decidable (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs as T
open import Definition.Typed.Properties senv equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Whnf senv swf equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Symmetry senv swf equivs
open import Definition.Conversion.SymmetrySize senv swf equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.StabilityProp senv swf equivs
open import Definition.Conversion.Conversion senv swf equivs
open import Definition.Conversion.ConversionProp senv swf equivs
open import Definition.Conversion.ConvSize senv equivs
open import Definition.Conversion.Lift senv swf equivs
open import Definition.Conversion.EqRelInstance senv swf equivs
open import Definition.Conversion.Inversion senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.Reduction senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Definition.Typed.Consequences.Inequality senv swf equivs as IE
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.SucCong senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Definition.Typed.Consequences.TypeUnicity senv swf equivs
open import Definition.Conversion.HelperDecidable senv swf equivs
open import Definition.Conversion.DecidableLemmas senv swf equivs
open import Definition.Conversion.DecView senv swf equivs
open import Definition.Conversion.Consequences.Completeness senv swf equivs
open import Definition.Conversion.TransitivityHelper
-- open import Definition.Conversion.Transitivity
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE
mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑! : ∀ {n k k' l l' R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
        → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
        → (size~↑! e + size~↑! e') << n
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↑! A ^ lA)

  dec~↑! {n = 0} _ _ _ ()

  -- general cases for t ~ cast _ _ e u

  dec~↑! {1+ n} Γ≡Δ X (cast-refl' A~A (ne-ins x' x₁' x₂' ([~] A₁' D₁' whnfB' k~l)) ⊢e') size =
    dec~↑! {n} Γ≡Δ X k~l (<<-trans <=-help-cast-refl'' (<=-help-cast-refl' size))

  dec~↑! {1+ n} Γ≡Δ (cast-refl' A~A (ne-ins x' x₁' x₂' ([~] A₁' D₁' whnfB' k~l)) ⊢e') X (leS size) =
    dec~↑! {n} Γ≡Δ k~l X (<<-trans (<=-help-b''x {a = 0} {b = size~↓! A~A}) size)

  dec~↑! {1+ n} Γ≡Δ X (castℕ-refl' ([~] A D whnfB k~l) ⊢e) size =
    dec~↑! {n} Γ≡Δ X k~l (<<-trans <=-help-ab1' (<=-help-cast-refl' size))

  dec~↑! {1+ n} Γ≡Δ (castℕ-refl' ([~] A D whnfB k~l) ⊢e) X (leS size) =
    dec~↑! {n} Γ≡Δ k~l X (<<-trans (le-suc (le-refl _)) size)

  -- diagonal cases

  dec~↑! Γ≡Δ (var-refl ⊢x e) (var-refl ⊢x' e') _ = dec-var-var Γ≡Δ ⊢x e ⊢x' e'

  dec~↑! Γ≡Δ (app-cong x~x t≡t) (app-cong y~y u≡u) (leS size) with dec~↓! Γ≡Δ x~x y~y (<=-trans (leS (<=-help-ab' {a = size~↓! x~x})) size)
  ... | yes (A , lA , x~y) =
    let
      whnfA , neK , neK₀ = ne~↓! x~y
      ⊢A , ⊢k , ⊢k₀ = syntacticEqTerm (soundness~↓! x~y)
      _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓! x~x)
      _ , ⊢k₂ , _ = syntacticEqTerm (soundness~↓! y~y)
      l₁≡lA , ΠFG≡A = neTypeEq neK ⊢k₁ ⊢k
      l₂≡lA , ΠF′G′≡A = neTypeEq neK₀ (stabilityTerm (symConEq Γ≡Δ) ⊢k₂) ⊢k₀
      l₂≡l₁ = ιinj (PE.trans l₂≡lA (PE.sym l₁≡lA))
      ΠFG≡ΠF′G′ = trans ΠFG≡A (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , ι X ]) l₂≡l₁ (sym ΠF′G′≡A))
      F≡F′ , rF≡rF′ , lF≡lF′ , lG≡lG′ , G≡G′ = injectivity ΠFG≡ΠF′G′
      ⊢k₁′ = PE.subst₄ (λ X Y Z T → _ ⊢ _ ∷ Π _ ^ X ° Y ▹ _ ° Z ° T ^ ! ^ [ ! , ι T ]) rF≡rF′ lF≡lF′ lG≡lG′ (PE.sym l₂≡l₁) ⊢k₁
      F≡F″ = (PE.subst₂ (λ X Y → _ ⊢ _ ≡ _ ^ [ X , ι Y ]) rF≡rF′ lF≡lF′ F≡F′)
    in PE.subst (λ X → Dec (∃ λ A → ∃ λ lA → _ ⊢ _ ∘ _ ^ X ~ _ ∘ _ ^ _ ↑! _ ^ _)) l₂≡l₁
      (dec~↑!-app Γ≡Δ ⊢k₁′ ⊢k₂ x~y (decConv↑TermConv′ Γ≡Δ (PE.sym (PE.cong₂ (λ X Y → [ X , ι Y ]) rF≡rF′ lF≡lF′)) PE.refl F≡F″ t≡t u≡u (<<-trans (<=-help-ab'' {a = size~↓! x~x}) size)))
  ... | no ¬p = no (λ { (_ , (_ , app-cong x′ y′)) → ¬p (_ , (_ , x′)) })

  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = l₀} G b0 bS k₀) (leS size) =
    dec-natrec-natrec Γ≡Δ F a0 aS k G b0 bS k₀
      (λ {PE.refl → decConv↑ (Γ≡Δ ∙ refl (univ (ℕⱼ (wfEqTerm (soundness~↓! k))))) F G (<<-trans (<=-help-nat-cong-ab {a = sizeConv↑ F}) size)})
      (λ {PE.refl p → decConv↑TermConv Γ≡Δ (substTypeEq (soundnessConv↑ p) (refl (zeroⱼ (wfEqTerm (soundness~↓! k))))) a0 b0 (<<-trans (<=-help-nat-congb'c' {a = sizeConv↑ F} {b = sizeConv↑ G}) size)})
      (λ {PE.refl p → decConv↑TermConv Γ≡Δ (sucCong (soundnessConv↑ p)) aS bS (<<-trans (<=-help-nat-congb''c'' {a = sizeConv↑ F} {b = sizeConv↑ G}) size)})
      (dec~↓! Γ≡Δ k k₀ (<<-trans (<=-help-nat-congb'''c''' {a = sizeConv↑ F} {b = sizeConv↑ G}) size))

  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = l₀} G k₀) (leS size) =
    dec-emptyrec-emptyrec Γ≡Δ F k G k₀
                          (λ {PE.refl → decConv↑ Γ≡Δ F G (<<-trans (<=-help-ab1' {a = sizeConv↑ F}) size)})

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB eAB') (cast-cong C D (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD eCD') (leS size) =
    let neA = proj₁ (proj₂ (ne~↓! A))
        neB = proj₁ (proj₂ (ne~↓! (sym~↓!U B)))
        neC = proj₁ (proj₂ (ne~↓! C))
        neD = proj₁ (proj₂ (ne~↓! (sym~↓!U D)))
        _ , ⊢A , _ = syntacticEqTerm (soundness~↓! A)
        _ , _ , ⊢B = syntacticEqTerm (soundness~↓! B)
        _ , ⊢C , _ = syntacticEqTerm (soundness~↓! C)
        _ , _ , ⊢D = syntacticEqTerm (soundness~↓! D)
    in cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD
                     (dec~↓! Γ≡Δ A C (<<-trans (<=-help-id-cong {a = size~↓! A} {b = size~↓! C}) size))
                     (dec~↓! (symConEq Γ≡Δ) (sym~↓!U D) (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize D) (sym~↓!Usize B))
                                                                      (+-sym (size~↓! D) (size~↓! B))) ) (<=-help-b'c' {a = size~↓! A} {b = size~↓! C})) size) )
                     (dec~↓! (reflConEq (wfTerm eAB)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B)))
                                                                              (<=-help-id-cong-ab' {a = size~↓! A} {b = size~↓! C} {b' = size~↓! B})) size))
                     (dec~↓! (reflConEq (wfTerm eCD)) C (sym~↓!U D) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! C)) (sym~↓!Usize D)))
                                                                              (<=-help-id-cong-bc' {a = size~↓! A} {b = size~↓! C} {b' = size~↓! B})) size))
                     (λ (_ , _ , A~C) →
                       decConv↓Term Γ≡Δ (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A C A~C (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)))
                          (<<-trans (PE.subst ( λ X →  (sizeConv↓Term (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) + X) <= _)
                                    (PE.sym (convert'~size Γ≡Δ A C A~C (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁))))
                                              (<=-help-b''c'' {a = size~↓! A } {b = size~↓! C} {b'' = 1+ (size~↓! ([~] A₁ D₁ whnfB k~l))}))
                                    size))
                     (dec~↑! Γ≡Δ k~l (cast-cong C D (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD eCD')
                                     (<<-trans (<=-help-cast {a = size~↓! A} {b = size~↓! B}) size))
                     (dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB eAB') k~l₁
                                 (<<-trans (<=-help-cast' {a = size~↓! A} {b = size~↓! C} {b' = size~↓! B} {c' = size~↓! D}) size))

  dec~↑! Γ≡Δ (cast-ℕ A t eℕA _) (cast-ℕ B u eℕB _) (leS size) =
    dec-castℕ-castℕ Γ≡Δ A t eℕA B u eℕB
                    (dec~↓! (symConEq Γ≡Δ) (sym~↓!U B) (sym~↓!U A) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize B) (sym~↓!Usize A))
                                                                      (+-sym (size~↓! B) (size~↓! A))) ) (<=-help-ab' {a = size~↓! A} {b = size~↓! B}))) size))
                    (decConv↑Term Γ≡Δ t u (<<-trans (<=-help-ab'' {a = size~↓! A} {c = size~↓! B}) size))

  dec~↑! Γ≡Δ (cast-Π {rA = r} Π A t eΠA _) (cast-Π {rA = r′} Π′ B u eΠB _) (leS size) =
    dec-castΠ-castΠ Γ≡Δ Π A t eΠA Π′ B u eΠB
                    (decConv↑Term Γ≡Δ Π Π′ (<<-trans (<=-help-id-cong {a = sizeConv↑Term Π}) size))
                    (dec~↓! (symConEq Γ≡Δ) (sym~↓!U B) (sym~↓!U A) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize B) (sym~↓!Usize A))
                                                                      (+-sym (size~↓! B) (size~↓! A))) ) (<=-help-b'c' {a = sizeConv↑Term Π} {b = sizeConv↑Term Π′}))) size))
                    (λ ΠΠ′ → decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term ΠΠ′)) t u (<<-trans (<=-help-b''c'' {a = sizeConv↑Term Π} {b = sizeConv↑Term Π′}) size))

  dec~↑! Γ≡Δ (cast-Πℕ {rA = r} Π t eΠℕ _) (cast-Πℕ {rA = r′} Π′ u eΠℕ′ _) (leS size) =
    dec-castΠℕ-castΠℕ Γ≡Δ t eΠℕ u eΠℕ′
                      (decConv↑Term Γ≡Δ Π Π′ (<<-trans (<=-help-ab' {a = sizeConv↑Term Π}) size))
                      (λ ΠΠ′ → decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term ΠΠ′)) t u (<<-trans (<=-help-ab'' {a = sizeConv↑Term Π} {c = sizeConv↑Term Π′}) size))

  dec~↑! Γ≡Δ (cast-ℕΠ {rA = r} Π t eΠℕ _) (cast-ℕΠ {rA = r′} Π′ u eΠℕ′ _) (leS size) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in dec-castℕΠ-castℕΠ Γ≡Δ t eΠℕ u eΠℕ′
                      (decConv↑Term (symConEq Γ≡Δ) (symConv↑Term (reflConEq ⊢Δ) Π′) (symConv↑Term (reflConEq ⊢Γ) Π)
                                              (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (size-symConv↑Term (reflConEq ⊢Δ) Π′) (size-symConv↑Term (reflConEq ⊢Γ) Π))
                                                                      (+-sym (sizeConv↑Term Π′) (sizeConv↑Term Π)))) (<=-help-ab' {a = sizeConv↑Term Π}))) size))
                      (decConv↑Term Γ≡Δ t u (<<-trans (<=-help-ab'' {a = sizeConv↑Term Π} {c = sizeConv↑Term Π′}) size))

  dec~↑! Γ≡Δ (cast-ΠΠ%! A B t eAB _) (cast-ΠΠ%! C D u eCD _) (leS size) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in dec-castΠΠ%!-castΠΠ%! Γ≡Δ t eAB u eCD
                          (decConv↑Term Γ≡Δ A C (<<-trans (<=-help-id-cong {a = sizeConv↑Term A}) size))
                          (decConv↑Term (symConEq Γ≡Δ) (symConv↑Term (reflConEq ⊢Δ) D) (symConv↑Term (reflConEq ⊢Γ) B) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (size-symConv↑Term (reflConEq ⊢Δ) D) (size-symConv↑Term (reflConEq ⊢Γ) B))
                                                                      (+-sym (sizeConv↑Term D) (sizeConv↑Term B)))) (<=-help-b'c' {a = sizeConv↑Term A} {b = sizeConv↑Term C}))) size))
                          (λ AC → decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term AC)) t u (<<-trans (<=-help-b''c'' {a = sizeConv↑Term A} {b = sizeConv↑Term C}) size))

  dec~↑! Γ≡Δ (cast-ΠΠ!% A B t eAB _) (cast-ΠΠ!% C D u eCD _) (leS size) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in dec-castΠΠ!%-castΠΠ!% Γ≡Δ t eAB u eCD
                          (decConv↑Term Γ≡Δ A C (<<-trans (<=-help-id-cong {a = sizeConv↑Term A}) size))
                          (decConv↑Term (symConEq Γ≡Δ) (symConv↑Term (reflConEq ⊢Δ) D) (symConv↑Term (reflConEq ⊢Γ) B) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (size-symConv↑Term (reflConEq ⊢Δ) D) (size-symConv↑Term (reflConEq ⊢Γ) B))
                                                                      (+-sym (sizeConv↑Term D) (sizeConv↑Term B)))) (<=-help-b'c' {a = sizeConv↑Term A} {b = sizeConv↑Term C}))) size))
                          (λ AC → decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term AC)) t u (<<-trans (<=-help-b''c'' {a = sizeConv↑Term A} {b = sizeConv↑Term C}) size))

  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-refl C~D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')) ⊢e') (leS size) =
    let _ , neA , neB = ne~↓! A~B
        _ , neC , neD = ne~↓! C~D
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
        _ , ⊢C , ⊢D = syntacticEqTerm (soundness~↓! C~D)
    in cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e'
                     (dec~↓! Γ≡Δ A~B C~D (<<-trans (<=-help-ab' {a = size~↓! A~B} {b = size~↓! C~D}) size))
                     (dec~↓! (symConEq Γ≡Δ) (sym~↓!U C~D) (sym~↓!U A~B) (<<-trans (<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize C~D) (sym~↓!Usize A~B))
                                                                      (+-sym (size~↓! C~D) (size~↓! A~B))) )
                                                                      (<=-help-ab' {a = size~↓! A~B} {b = size~↓! C~D})) size) )
                     (yes (_ , _ , A~B))
                     (yes (_ , _ , C~D))
                     (λ (_ , _ , A~C) →
                       decConv↓Term Γ≡Δ (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A~B C~D A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')))
                          (<<-trans (PE.subst ( λ X →  (sizeConv↓Term (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) + X) <= _)
                                    (PE.sym (convert'~size Γ≡Δ A~B C~D A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))))
                                              (<=-help-ab'' {a = size~↓! A~B} {c = size~↓! C~D}))
                                    size))
                     (dec~↑! Γ≡Δ k~l (cast-refl C~D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')) ⊢e')
                                     (<<-trans (<=-help-b''x {a = 0} {b = size~↓! A~B}) size))
                     (dec~↑! Γ≡Δ (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) k~l'
                                 (<<-trans (<=-help-ab'c'' {a = size~↓! A~B} {b = 0} {c' = size~↓! C~D}) size))

  dec~↑! Γ≡Δ (castℕ-refl t eℕℕ) (castℕ-refl u eℕℕ′) (leS size) =
    dec-castℕrefl-castℕrefl Γ≡Δ t eℕℕ u eℕℕ′ (dec~↓! Γ≡Δ t u (<<-trans (<=-help-ab1' {a = size~↓! t}) size))

  dec~↑! Γ≡Δ (cast-neℕ A t eℕA _) (cast-neℕ B u eℕB _) (leS size) =
    dec-castneℕ-castneℕ Γ≡Δ A t eℕA B u eℕB
                        (dec~↓! Γ≡Δ A B (<<-trans (<=-help-ab' {a = size~↓! A} {b = size~↓! B}) size))
                        (λ (_ , _ , AB) → decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A B AB u) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (sizeConv↑Term t)) (convert~size Γ≡Δ A B AB u)))
                                                                                               (<=-help-ab'' {a = size~↓! A} {c = size~↓! B} )) size))

  dec~↑! Γ≡Δ (cast-neΠ {rA = r} Π~Π A t eℕA _) (cast-neΠ {rA = r'} Π~Π' B u eℕB _) (leS size) =
    dec-castneΠ-castneΠ Γ≡Δ A t eℕA B u eℕB
                        (dec~↓! Γ≡Δ A B (<<-trans (<=-help-b'c' {a = sizeConv↑Term Π~Π} {b = sizeConv↑Term Π~Π'}) size))
                        (decConv↑Term Γ≡Δ (symConv↑Term (symConEq Γ≡Δ) Π~Π') (symConv↑Term Γ≡Δ Π~Π) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (size-symConv↑Term (symConEq Γ≡Δ) Π~Π') (size-symConv↑Term Γ≡Δ Π~Π))
                                                                      (+-sym (sizeConv↑Term Π~Π') (sizeConv↑Term Π~Π)))) (<=-help-id-cong {a = sizeConv↑Term Π~Π} {b = sizeConv↑Term Π~Π'}))) size) )
                        (λ (_ , _ , AB) → decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A B AB u) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (sizeConv↑Term t)) (convert~size Γ≡Δ A B AB u)))
                                                                        (<=-help-b''c'' {a = sizeConv↑Term Π~Π} {b = sizeConv↑Term Π~Π'})) size))

  -- antidiagonal cases

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (app-cong x~x t≡t) _ = not-diag~↑! Γ≡Δ (var-refl ⊢x n≡n) (app-cong x~x t≡t) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (natrec-cong x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (natrec-cong x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (Emptyrec-cong x x₁) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (Emptyrec-cong x x₁) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ℕ x X x₂ x₃) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ℕ x X x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-Π x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-Π x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-Πℕ x x₁ x₂ x₃) _ =  not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-Πℕ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ℕΠ x x₁ x₂ x₃) _ =  not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ℕΠ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) PE.refl

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                    (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                    (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                    (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                  (<=-help-abrem {x = 0} {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                    (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (<=-help-abrem' {x = 1} {a = size~↓! A + size~↓! B} {b = 1 + size~↑! k~l}) size))
                    (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (var-refl ⊢x n≡n) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (<=-help-abrem' {x = 1} {a = size~↓! A~A} {b = 1 + size~↑! k~l}) size))
                      (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (var-refl ⊢x n≡n) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                     (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                     (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (le-suc (le-refl _)) size))
                     (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (var-refl x x₁) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                         (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (var-refl x x₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (app-cong x~x t≡t) (var-refl x x₁) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (var-refl x x₁) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (natrec-cong x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (natrec-cong x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Emptyrec-cong x x₁) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (Emptyrec-cong x x₁) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Πℕ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Πℕ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕΠ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕΠ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = app-cong x~x t≡t
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = app-cong x~x t≡t
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = app-cong x~x t≡t
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () }) (λ { () })

  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (var-refl x₄ x₅) _ = not-diag~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (var-refl x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (app-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (app-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Π x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Π x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Πℕ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Πℕ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕΠ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕΠ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = natrec-cong x' x'₁ x'₂ x'₃
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (natrec-cong x' x'₁ x'₂ x'₃)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (natrec-cong x' x'₁ x'₂ x'₃)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () }) (λ { () })

  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl x₂ x₃) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₂ x₃) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Πℕ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Πℕ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = Emptyrec-cong x' x'₁
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Emptyrec-cong x' x'₁)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Emptyrec-cong x' x'₁)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () }) (λ { () })

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (var-refl {n} ⊢x n≡n) (leS size) =
    let X = var-refl ⊢x n≡n
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ {_ _ ()}) (λ {()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (app-cong x₅ x₆) (leS size) =
    let X = app-cong x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ {_ _ ()}) (λ {()}) (λ {()})

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (natrec-cong x₅ x₆ x₇ x₈) (leS size) =
    let X = natrec-cong x₅ x₆ x₇ x₈
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ {_ _ ()}) (λ {()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Emptyrec-cong x₅ x₆) (leS size) =
    let X = Emptyrec-cong x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ {_ _ ()}) (λ {()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ℕ x₅ x₆ x₇ x₈) (leS size) =
    let X = cast-ℕ x₅ x₆ x₇ x₈
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeℕ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! x₅
                             in noNeℕ (PE.subst Neutral eB neB))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! x₅
                             in noNeInd (PE.subst Neutral eB neB))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-Π x₅ x₆ x₇ x₈ x₉) (leS size) =
    let X = cast-Π x₅ x₆ x₇ x₈ x₉
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! x₆
                             in noNeℕ (PE.subst Neutral eB neB))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! x₆
                             in noNeInd (PE.subst Neutral eB neB))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-Πℕ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-refl C~D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')) ⊢e'') (leS size) =
    let neA = proj₁ (proj₂ (ne~↓! A))
        neB = proj₁ (proj₂ (ne~↓! (sym~↓!U B)))
        _ , neC , neD = ne~↓! C~D
        _ , ⊢A , _ = syntacticEqTerm (soundness~↓! A)
        _ , _ , ⊢B = syntacticEqTerm (soundness~↓! B)
        _ , ⊢C , ⊢D = syntacticEqTerm (soundness~↓! C~D)
    in cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e''
                     (dec~↓! Γ≡Δ A C~D (<<-trans (<=-help-id-cong-c'' {a = size~↓! A} {b = size~↓! C~D}) size))
                     (dec~↓! (symConEq Γ≡Δ) (sym~↓!U C~D) (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize C~D) (sym~↓!Usize B))
                                                                      (+-sym (size~↓! C~D) (size~↓! B))) )
                                                                      (<=-help-b'b-c'' {a = size~↓! A} {b = size~↓! C~D})) size) )
                     (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B)))
                                                                              (<=-help-id-cong-ab' {a = size~↓! A} {b = 0} {c' = size~↓! C~D})) size))
                     (yes (_ , _ , C~D))
                     (λ (_ , _ , A~C) →
                       decConv↓Term Γ≡Δ (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A C~D A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')))
                          (<<-trans (PE.subst ( λ X →  (sizeConv↓Term (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) + X) <= _)
                                    (PE.sym (convert'~size Γ≡Δ A C~D A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))))
                                              (<=-help-b''-c'' {a = size~↓! A} {b = size~↓! C~D}))
                                    size))
                     (dec~↑! Γ≡Δ k~l (cast-refl C~D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')) ⊢e'')
                                     (<<-trans (<=-help-b''x {a = size~↓! A}) size))
                     (dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') k~l'
                                 (<<-trans (<=-help-ab'b''c'' {a = size~↓! A} {b = size~↓! C~D}) size))

  dec~↑! Γ≡Δ (cast-cong A B _ _ _) (castℕ-refl _ _) (leS size) =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-neℕ x₂' x₃' x₄' x₅') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                            in ℕ≢ne! neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-neΠ x₂' x'₃ x₄' x'₅ x₆') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                            in IE.Π≢ne neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (var-refl x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (var-refl x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (app-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (app-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-ℕ x₄ x₅ x₆ x₇) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (leS size) =
    let X = cast-ℕ x₄ x₅ x₆ x₇
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eA) neA) })
                       (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                    _ , _ , neB = ne~↓! x₄
                              in noNeℕ (PE.subst Neutral eB neB) })
                       (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                    _ , _ , neB = ne~↓! x₄
                              in noNeInd (PE.subst Neutral eB neB) })

  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-ℕ x' x₁' x₂' x₃')
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eA) neA) })
                      (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                   _ , _ , neB = ne~↓! x'
                               in noNeℕ (PE.subst Neutral eB neB) })
                      (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                   _ , _ , neB = ne~↓! x'
                               in noNeInd (PE.subst Neutral eB neB) })
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (cast-ℕ x' x₁' x₂' x₃')
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eA) neA) })
                           (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                        _ , _ , neB = ne~↓! x'
                                    in noNeℕ (PE.subst Neutral eB neB) })
                           (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                        _ , _ , neB = ne~↓! x'
                                    in noNeInd (PE.subst Neutral eB neB) })

  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ = not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) PE.refl
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ = not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) PE.refl
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-Π x₅ x₆ x₇ x₈ x₉) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (leS size) =
    let X = cast-Π x₅ x₆ x₇ x₈ x₉
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ ,  neB = ne~↓! x₆
                             in noNeℕ (PE.subst Neutral eB neB))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ ,  neB = ne~↓! x₆
                             in noNeInd (PE.subst Neutral eB neB))
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-refl  A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = cast-Π x' B x₁' x₂' x₃'
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! B
                             in noNeℕ (PE.subst Neutral eB neB))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! B
                             in noNeInd (PE.subst Neutral eB neB))

  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (castℕ-refl x₅ x₆) _ =
      no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                          in ℕ≢ne! neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x₃ x₄ x₅ x₆) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = cast-Πℕ x₃ x₄ x₅ x₆
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeΠ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })
                         (λ { () })

  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ℕΠ x₃ x₄ x₅ x₆) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = cast-ℕΠ x₃ x₄ x₅ x₆
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeℕ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })
                         (λ { () })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))

  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% A x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% A x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = cast-ΠΠ%! x x₁ x₂ x₃ x₄
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeΠ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })
                         (λ { () })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))

  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! A x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! A x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = cast-ΠΠ!% x x₁ x₂ x₃ x₄
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeΠ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })
                         (λ { () })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))

  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-cong C D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))  ⊢e' ⊢e'') (leS size) =
    let neC = proj₁ (proj₂ (ne~↓! C))
        neD = proj₁ (proj₂ (ne~↓! (sym~↓!U D)))
        _ , neA , neB = ne~↓! A~B
        _ , ⊢C , _ = syntacticEqTerm (soundness~↓! C)
        _ , _ , ⊢D = syntacticEqTerm (soundness~↓! D)
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e'
                     (dec~↓! Γ≡Δ A~B C (<<-trans (<=-help-ab-c'' {a = size~↓! A~B} {b = size~↓! C}) size))
                     (dec~↓! (symConEq Γ≡Δ) (sym~↓!U D) (sym~↓!U A~B) (<<-trans (<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize D) (sym~↓!Usize A~B))
                                                                      (+-sym (size~↓! D) (size~↓! A~B))) )
                                                                      (<=-help-ac'-c'' {a = size~↓! A~B} {b = size~↓! C})) size) )
                     (yes (_ , _ , A~B))
                     (dec~↓! (reflConEq (wfTerm ⊢e')) C (sym~↓!U D) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! C)) (sym~↓!Usize D)))
                                                                              (<=-help-bc'-c'' {a = size~↓! A~B} {b = size~↓! C})) size))
                     (λ (_ , _ , A~C) →
                       decConv↓Term Γ≡Δ (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A~B C A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')))
                          (<<-trans (PE.subst ( λ X →  (sizeConv↓Term (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) + X) <= _)
                                    (PE.sym (convert'~size Γ≡Δ A~B C A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))))
                                              (<=-help-b'c'' {a = size~↓! A~B} {b = size~↓! C}))
                                    size))
                     (dec~↑! Γ≡Δ k~l (cast-cong C D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))  ⊢e' ⊢e'')
                                     (<<-trans (<=-help-b''x {a = 0} {b = size~↓! A~B}) size))
                     (dec~↑! Γ≡Δ (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) k~l'
                                 (<<-trans (<=-help-ab'c'' {a = size~↓! A~B} {b = size~↓! C}) size))

  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (var-refl {n} ⊢x n≡n) (leS size) =
    let X = var-refl ⊢x n≡n
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ {_ _ ()}) (λ {()}) (λ {()})
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (app-cong x₅ x₆) (leS size) =
    let X = app-cong x₅ x₆
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ {_ _ ()}) (λ {()}) (λ {()})

  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (natrec-cong x₅ x₆ x₇ x₈) (leS size) =
    let X = natrec-cong x₅ x₆ x₇ x₈
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ {_ _ ()}) (λ {()}) (λ {()})
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (Emptyrec-cong x₅ x₆) (leS size) =
    let X = Emptyrec-cong x₅ x₆
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ {_ _ ()}) (λ {()}) (λ {()})
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-ℕ x₅ x₆ x₇ x₈) (leS size) =
    let X = cast-ℕ x₅ x₆ x₇ x₈
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                    in noNeℕ (PE.subst Neutral (PE.sym eA) neA))
                     (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                _ , _ , neB = ne~↓! x₅
                            in noNeℕ (PE.subst Neutral eB neB))
                     (λ {()})
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-Π x₅ x₆ x₇ x₈ x₉) (leS size) =
    let X = cast-Π x₅ x₆ x₇ x₈ x₉
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! x₆
                             in noNeℕ (PE.subst Neutral eB neB))
                      (λ {()})
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-Πℕ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl B _ _) (castℕ-refl _ _) (leS size) =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-neℕ x₂' x₃' x₄' x₅') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                            in ℕ≢ne! neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-neΠ x₂' x'₃ x₄' x'₅ x₆') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                            in IE.Π≢ne neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (var-refl x₃ x₄) (leS size) =
    let X = var-refl x₃ x₄
    in castℕℕ-refl-dec~ ([~] A D whnfB k~l) ⊢e
                       (dec~↑! Γ≡Δ k~l X (<<-trans (le-suc (le-refl _)) size))
                       (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (app-cong x₃ x₄) (leS size) =
    let X = app-cong x₃ x₄
    in castℕℕ-refl-dec~ ([~] A D whnfB k~l) ⊢e
                       (dec~↑! Γ≡Δ k~l X (<<-trans (le-suc (le-refl _)) size))
                       (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (natrec-cong x₃ x₄ x₅ x₆) (leS size) =
    let X = natrec-cong x₃ x₄ x₅ x₆
    in castℕℕ-refl-dec~ ([~] A D whnfB k~l) ⊢e
                       (dec~↑! Γ≡Δ k~l X (<<-trans (le-suc (le-refl _)) size))
                       (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (Emptyrec-cong x₃ x₄) (leS size) =
    let X = Emptyrec-cong x₃ x₄
    in castℕℕ-refl-dec~ ([~] A D whnfB k~l) ⊢e
                       (dec~↑! Γ≡Δ k~l X (<<-trans (le-suc (le-refl _)) size))
                       (λ { _ _ () }) (λ { () }) (λ { () })
  dec~↑! Γ≡Δ (castℕ-refl x ⊢e) (cast-cong A B x₅ x₆ x₇) _ =
      no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                          in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (castℕ-refl x x₁) (cast-ℕ B x₄ x₅ x₆) _ =
      no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                          in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (castℕ-refl x x₁) (cast-Π x₃ B x₅ x₆ x₇) _ =
      no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                          in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (cast-Πℕ x₃ x₄ x₅ x₆) (leS size) =
    let X = cast-Πℕ x₃ x₄ x₅ x₆
    in castℕℕ-refl-dec~ ([~] A D whnfB k~l) ⊢e
                       (dec~↑! Γ≡Δ k~l X (<<-trans (le-suc (le-refl _)) size))
                       (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                        in noNeΠ (PE.subst Neutral (PE.sym eA) neA)})
                       (λ { () })
                       (λ { () })
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (cast-ℕΠ x₃ x₄ x₅ x₆) (leS size) =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (cast-ΠΠ%! x₃ x₄ x₅ x₆ x₇) (leS size) =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (cast-ΠΠ!% x₃ x₄ x₅ x₆ x₇) (leS size) =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (cast-neΠ x x₁ x₂ x₃ x₄) (leS size) =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  dec~↑! Γ≡Δ (castℕ-refl x ⊢e) (cast-refl B x₅ x₆) _ =
      no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                          in ℕ≢ne! neR (cast-cast-≡ X))

  dec~↑! Γ≡Δ (castℕ-refl ([~] A D whnfB k~l) ⊢e) (cast-neℕ x x₁ x₂ x₃) (leS size) =
    let X = cast-neℕ x x₁ x₂ x₃
    in castℕℕ-refl-dec~ ([~] A D whnfB k~l) ⊢e
                       (dec~↑! Γ≡Δ k~l X (<<-trans (le-suc (le-refl _)) size))
                       (λ { neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e
                                        in noNeℕ (PE.subst Neutral (PE.sym eB) neB)})
                       (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! x
                                in noNeℕ (PE.subst Neutral eA neA) })
                       (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! x
                                in noNeInd (PE.subst Neutral eA neA) })
  dec~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (var-refl x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (var-refl x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (app-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (app-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ x' x₁' x₂' x₃') (cast-ℕ x₂ x₃ x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neℕ x' x₁' x₂' x₃') (cast-ℕ x₂ x₃ x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-neℕ x₁ x₂ x₃ x₄) (cast-neΠ x₅ x₆ x₇ x₈ x₉) _ = not-diag~↑! Γ≡Δ (cast-neℕ x₁ x₂ x₃ x₄) (cast-neΠ x₅ x₆ x₇ x₈ x₉) PE.refl

  dec~↑! Γ≡Δ (cast-neℕ x₄ x₅ x₆ x₇) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (leS size) =
    let X = cast-neℕ x₄ x₅ x₆ x₇
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eB) neB) })
                       (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! x₄
                              in noNeℕ (PE.subst Neutral eA neA) })
                       (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! x₄
                              in noNeInd (PE.subst Neutral eA neA) })
  dec~↑! Γ≡Δ (cast-neℕ x' x₁' x₂' x₃') (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-neℕ x' x₁' x₂' x₃')
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eB) neB) } )
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x'
                               in noNeℕ (PE.subst Neutral eA neA) })
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x'
                               in noNeInd (PE.subst Neutral eA neA) })
  dec~↑! Γ≡Δ (cast-neℕ x' x₁' x₂' x₃') (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (cast-neℕ x' x₁' x₂' x₃')
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                      (λ { neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eB) neB) } )
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x'
                               in noNeℕ (PE.subst Neutral eA neA) })
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x'
                               in noNeInd (PE.subst Neutral eA neA) })
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (var-refl x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (var-refl x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (app-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (app-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-ℕ x₂ x₃ x₄' x₅') _ = not-diag~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-ℕ x₂ x₃ x₄' x₅') PE.refl
  dec~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-neℕ x₂ x₃ x₄' x₅') _ = not-diag~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-neℕ x₂ x₃ x₄' x₅') PE.refl
  dec~↑! Γ≡Δ (cast-neΠ Π x₄' x₅' x₆' x₇') (cast-ℕΠ x₄ x₅ x₆ x₇) _ = not-diag~↑! Γ≡Δ (cast-neΠ Π x₄' x₅' x₆' x₇') (cast-ℕΠ x₄ x₅ x₆ x₇) PE.refl

  dec~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (leS size) =
    let X = cast-neΠ Π x₄ x₅ x₆ x₇
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eB) neB) })
                       (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! x₄
                              in noNeℕ (PE.subst Neutral eA neA) })
                       (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! x₄
                              in noNeInd (PE.subst Neutral eA neA) })
  dec~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-neΠ Π x₄ x₅ x₆ x₇)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eB) neB) } )
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x₄
                               in noNeℕ (PE.subst Neutral eA neA) })
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x₄
                               in noNeInd (PE.subst Neutral eA neA) })
  dec~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (cast-neΠ Π x₄ x₅ x₆ x₇)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                      (λ { neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eB) neB) } )
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x₄
                               in noNeℕ (PE.subst Neutral eA neA) })
                      (λ { e → let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x₄
                               in noNeInd (PE.subst Neutral eA neA) })