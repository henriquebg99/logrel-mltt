import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.Decidable (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs as T
open import Definition.Typed.Properties senv swf equivs
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
open import Tools.Unit
open import Tools.Nullary
open import Tools.List using (All₂; All₃; []ₐ; _∷ₐ_)
import Tools.List as L
open import Definition.Typed.Consequences.IndRectCong senv swf equivs using (indRectBranchTyListEq)
import Tools.PropositionalEquality as PE

-- Decidability of All₃ on a cons, from decidability of its head and tail.
-- decConv↑TermAll uses this instead of with: abstracting over calls of
-- the decision procedure makes Agda evaluate them and exhaust the heap.
dec∷ₐ : ∀ {A B C : Set} {P : A → B → C → Set} {x y z xs ys zs}
      → Dec (P x y z) → Dec (All₃ P xs ys zs) → Dec (All₃ P (x L.∷ xs) (y L.∷ ys) (z L.∷ zs))
dec∷ₐ (yes r) (yes rs) = yes (r ∷ₐ rs)
dec∷ₐ (yes r) (no ¬rs) = no λ { (_ ∷ₐ rs) → ¬rs rs }
dec∷ₐ (no ¬r) _ = no λ { (r ∷ₐ _) → ¬r r }

-- A conversion at a neutral type is necessarily an ne-ins.
-- dec~↑! uses this eliminator instead of nested ne-ins patterns: with nested
-- patterns, coverage checking has to refute every other [conv↓] constructor
-- again for each clause, which is very slow. It is also used instead of a
-- view with `with`, since each with-function adds all its arguments to the
-- positivity check of the mutual block, which then takes very long.
neInsElim : ∀ {Γ t u A} (P : Γ ⊢ t [conv↓] u ∷ A ^ ι ⁰ → Set)
          → Neutral A → (t≡u : Γ ⊢ t [conv↓] u ∷ A ^ ι ⁰)
          → (∀ {M} ⊢t ⊢u neA A₁ D₁ whnfM (k~l : Γ ⊢ t ~ u ↑! A₁ ^ ι ⁰)
             → P (ne-ins {M = M} ⊢t ⊢u neA ([~] A₁ D₁ whnfM k~l)))
          → P t≡u
neInsElim P _ (ne-ins ⊢t ⊢u neA ([~] A₁ D₁ whnfM k~l)) k = k ⊢t ⊢u neA A₁ D₁ whnfM k~l
neInsElim P () (ne _) k
neInsElim P () (Π-cong _ _ _ _ _ _ _ _ _) k
neInsElim P () (Ind-ins _) k
neInsElim P () (η-eq _ _ _ _ _ _ _ _) k
neInsElim P () (ctr-cong _ _ _ _) k

-- Terms whose head is visibly not a cast.
NotCast : Term → Set
NotCast (gen (Castkind _) _) = ⊥
NotCast _ = ⊤

-- The mutual block below uses this with plain lambdas, e.g. (λ _ _ → ≢cast _),
-- instead of absurd pattern lambdas: every pattern lambda becomes a definition
-- of the mutual block taking the whole context as arguments, which makes the
-- positivity check of the block very slow.
≢cast : ∀ {u l A B e t} → NotCast u → u PE.≡ cast l A B e t → ⊥
≢cast nc PE.refl = nc

-- Terms that are visibly not casts between inductive types.

NotCastIndInd : Term → Set
NotCastIndInd (gen (Castkind _) (⟦ _ , gen (Indkind _) L.[] ⟧ L.∷ ⟦ _ , gen (Indkind _) L.[] ⟧ L.∷ _)) = ⊥
NotCastIndInd _ = ⊤


≢castIndInd : ∀ {u l i e t} → NotCastIndInd u → u PE.≡ cast l (Ind i) (Ind i) e t → ⊥
≢castIndInd nc PE.refl = nc

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

  dec~↑! {1+ n} Γ≡Δ X (cast-refl' A~A ne≡1 ⊢e') size =
    neInsElim (λ ne≡1 → (size~↑! X + size~↑! (cast-refl' A~A ne≡1 ⊢e')) << _ → Dec _) (proj₂ (proj₂ (ne~↓! A~A))) ne≡1 (λ x' x₁' x₂' A₁' D₁' whnfB' k~l size →
    dec~↑! {n} Γ≡Δ X k~l (<<-trans <=-help-cast-refl'' (<=-help-cast-refl' size))
    ) size

  dec~↑! {1+ n} Γ≡Δ (cast-refl' A~A ne≡1 ⊢e') X (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl' A~A ne≡1 ⊢e') + size~↑! X) <= _ → Dec _) (proj₂ (proj₂ (ne~↓! A~A))) ne≡1 (λ x' x₁' x₂' A₁' D₁' whnfB' k~l size →
    dec~↑! {n} Γ≡Δ k~l X (<<-trans (<=-help-b''x {a = 0} {b = size~↓! A~A}) size)
    ) size



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


  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = l₀} G k₀) (leS size) =
    dec-emptyrec-emptyrec Γ≡Δ F k G k₀
                          (λ {PE.refl → decConv↑ Γ≡Δ F G (<<-trans (<=-help-ab1' {a = sizeConv↑ F}) size)})

  dec~↑! Γ≡Δ (cast-cong A B ne≡1 eAB eAB') (cast-cong C D ne≡2 eCD eCD') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 eAB eAB') + size~↑! (cast-cong C D ne≡2 eCD eCD')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ ⊢t x₁ x₂ A₁ D₁ whnfB k~l size →
    neInsElim (λ ne≡2 → (size~↑! (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB eAB') + size~↑! (cast-cong C D ne≡2 eCD eCD')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! C))) ne≡2 (λ ⊢u x₄ x₅ A₂ D₂ whnfB₁ k~l₁ size →
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
    ) size) size


  dec~↑! Γ≡Δ (cast-Π {rA = r} Π A t eΠA _) (cast-Π {rA = r′} Π′ B u eΠB _) (leS size) =
    dec-castΠ-castΠ Γ≡Δ Π A t eΠA Π′ B u eΠB
                    (decConv↑Term Γ≡Δ Π Π′ (<<-trans (<=-help-id-cong {a = sizeConv↑Term Π}) size))
                    (dec~↓! (symConEq Γ≡Δ) (sym~↓!U B) (sym~↓!U A) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize B) (sym~↓!Usize A))
                                                                      (+-sym (size~↓! B) (size~↓! A))) ) (<=-help-b'c' {a = sizeConv↑Term Π} {b = sizeConv↑Term Π′}))) size))
                    (λ ΠΠ′ → decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term ΠΠ′)) t u (<<-trans (<=-help-b''c'' {a = sizeConv↑Term Π} {b = sizeConv↑Term Π′}) size))



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

  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (cast-refl C~D ne≡2 ⊢e') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (cast-refl C~D ne≡2 ⊢e')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ ⊢t x₁ x₂ A₁ D₁ whnfB k~l size →
    neInsElim (λ ne≡2 → (size~↑! (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) + size~↑! (cast-refl C~D ne≡2 ⊢e')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! C~D))) ne≡2 (λ ⊢u x₁' x₂' A₁' D₁' whnfB' k~l' size →
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
    ) size) size




  -- antidiagonal cases

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (app-cong x~x t≡t) _ = not-diag~↑! Γ≡Δ (var-refl ⊢x n≡n) (app-cong x~x t≡t) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (Emptyrec-cong x x₁) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (Emptyrec-cong x x₁) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-Π x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-Π x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (var-refl  ⊢x n≡n) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) PE.refl

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-cong A B ne≡1 ⊢e w1) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (var-refl ⊢x n≡n) + size~↑! (cast-cong A B ne≡1 ⊢e w1)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                    (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                    (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                    (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                  (<=-help-abrem {x = 0} {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                    (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (<=-help-abrem' {x = 1} {a = size~↓! A + size~↓! B} {b = 1 + size~↑! k~l}) size))
                    (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (var-refl ⊢x n≡n) (cast-refl A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (var-refl ⊢x n≡n) + size~↑! (cast-refl A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (<=-help-abrem' {x = 1} {a = size~↓! A~A} {b = 1 + size~↑! k~l}) size))
                      (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (var-refl x x₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (cast-neΠ {rA = r} Π~Π A t eℕA _) (cast-neΠ {rA = r'} Π~Π' B u eℕB _) (leS size) =
    dec-castneΠ-castneΠ Γ≡Δ A t eℕA B u eℕB
                        (dec~↓! Γ≡Δ A B (<<-trans (<=-help-b'c' {a = sizeConv↑Term Π~Π} {b = sizeConv↑Term Π~Π'}) size))
                        (decConv↑Term Γ≡Δ (symConv↑Term (symConEq Γ≡Δ) Π~Π') (symConv↑Term Γ≡Δ Π~Π) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (size-symConv↑Term (symConEq Γ≡Δ) Π~Π') (size-symConv↑Term Γ≡Δ Π~Π))
                                                                      (+-sym (sizeConv↑Term Π~Π') (sizeConv↑Term Π~Π)))) (<=-help-id-cong {a = sizeConv↑Term Π~Π} {b = sizeConv↑Term Π~Π'}))) size) )
                        (λ (_ , _ , AB) → decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A B AB u) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (sizeConv↑Term t)) (convert~size Γ≡Δ A B AB u)))
                                                                        (<=-help-b''c'' {a = sizeConv↑Term Π~Π} {b = sizeConv↑Term Π~Π'})) size))


  dec~↑! Γ≡Δ (app-cong x~x t≡t) (var-refl x x₁) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (var-refl x x₁) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Emptyrec-cong x x₁) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (Emptyrec-cong x x₁) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-cong A B ne≡1 ⊢e w2) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (app-cong x~x t≡t) + size~↑! (cast-cong A B ne≡1 ⊢e w2)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
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
                       (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-refl A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (app-cong x~x t≡t) + size~↑! (cast-refl A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = app-cong x~x t≡t
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ _ _ → ≢cast _) (≢cast _)
    ) size



  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl x₂ x₃) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₂ x₃) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₂ x₃) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-cong A B ne≡1 ⊢e w4) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (Emptyrec-cong x' x'₁) + size~↑! (cast-cong A B ne≡1 ⊢e w4)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
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
                       (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-refl A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (Emptyrec-cong x' x'₁) + size~↑! (cast-refl A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = (Emptyrec-cong x' x'₁)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ _ _ → ≢cast _) (≢cast _)
    ) size

  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (var-refl {n} ⊢x n≡n) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 ⊢e ⊢e') + size~↑! (var-refl ⊢x n≡n)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = var-refl ⊢x n≡n
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (app-cong x₅ x₆) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 ⊢e ⊢e') + size~↑! (app-cong x₅ x₆)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = app-cong x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ _ _ → ≢cast _) (≢cast _)
    ) size

  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (Emptyrec-cong x₅ x₆) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 ⊢e ⊢e') + size~↑! (Emptyrec-cong x₅ x₆)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = Emptyrec-cong x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (cast-Π x₅ x₆ x₇ x₈ x₉) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 ⊢e ⊢e') + size~↑! (cast-Π x₅ x₆ x₇ x₈ x₉)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-Π x₅ x₆ x₇ x₈ x₉
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , _ , neB = ne~↓! x₆
                             in noNeInd (PE.subst Neutral eB neB))
    ) size
  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (cast-refl C~D ne≡2 ⊢e'') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 ⊢e ⊢e') + size~↑! (cast-refl C~D ne≡2 ⊢e'')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ ⊢t x₁ x₂ A₁ D₁ whnfB k~l size →
    neInsElim (λ ne≡2 → (size~↑! (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') + size~↑! (cast-refl C~D ne≡2 ⊢e'')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! C~D))) ne≡2 (λ ⊢u x₁' x₂' A₁' D₁' whnfB' k~l' size →
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
    ) size) size



  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (cast-neΠ x₂' x'₃ x₄' x'₅ x₆') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                            in IE.Π≢ne neR (sym (cast-cast-≡ X)))




  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ = not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) PE.refl
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ = not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) PE.refl
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-Π x₅ x₆ x₇ x₈ x₉) (cast-cong A B ne≡1 ⊢e ⊢e') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-Π x₅ x₆ x₇ x₈ x₉) + size~↑! (cast-cong A B ne≡1 ⊢e ⊢e')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
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
                             in noNeInd (PE.subst Neutral eB neB))
    ) size
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-refl  A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-Π x' B x₁' x₂' x₃') + size~↑! (cast-refl  A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
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
                             in noNeInd (PE.subst Neutral eB neB))
    ) size






  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% A x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% A x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))

  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! A x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! A x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) PE.refl

  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))

  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (cast-cong C D ne≡2  ⊢e' ⊢e'') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (cast-cong C D ne≡2  ⊢e' ⊢e'')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ ⊢t x₁ x₂ A₁ D₁ whnfB k~l size →
    neInsElim (λ ne≡2 → (size~↑! (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) + size~↑! (cast-cong C D ne≡2  ⊢e' ⊢e'')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! C))) ne≡2 (λ ⊢u x₁' x₂' A₁' D₁' whnfB' k~l' size →
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
    ) size) size

  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (var-refl {n} ⊢x n≡n) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (var-refl ⊢x n≡n)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = var-refl ⊢x n≡n
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (app-cong x₅ x₆) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (app-cong x₅ x₆)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = app-cong x₅ x₆
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ _ _ → ≢cast _) (≢cast _)
    ) size

  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (Emptyrec-cong x₅ x₆) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (Emptyrec-cong x₅ x₆)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = Emptyrec-cong x₅ x₆
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (cast-Π x₅ x₆ x₇ x₈ x₉) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (cast-Π x₅ x₆ x₇ x₈ x₉)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-Π x₅ x₆ x₇ x₈ x₉
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (≢castIndInd _)
    ) size
  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (cast-neΠ x₂' x'₃ x₄' x'₅ x₆') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! A~B
                            in IE.Π≢ne neR (sym (cast-cast-≡ X)))



  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (var-refl x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (var-refl x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (app-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (app-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ = not-diag~↑! Γ≡Δ (cast-neΠ X x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) PE.refl

  dec~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-cong A B ne≡1 ⊢e ⊢e') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-neΠ Π x₄ x₅ x₆ x₇) + size~↑! (cast-cong A B ne≡1 ⊢e ⊢e')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
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
                       (λ neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eB) neB))
                       (λ e →   let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! x₄
                              in noNeInd (PE.subst Neutral eA neA))
    ) size
  dec~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-refl A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-neΠ Π x₄ x₅ x₆ x₇) + size~↑! (cast-refl A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = (cast-neΠ Π x₄ x₅ x₆ x₇)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eB) neB) )
                      (λ e →   let _ , eA , _ = cast-PE-injectivity e
                                   _ , neA , _ = ne~↓! x₄
                               in noNeInd (PE.subst Neutral eA neA))
    ) size

  dec~↑! Γ≡Δ (IndRect-cong ind∈ P t ms) (IndRect-cong ind∈' Q u ns) (leS size) =
    dec-IndRect-IndRect ind∈ ind∈' t
      (λ {PE.refl PE.refl → decConv↑ (Γ≡Δ ∙ refl (univ (Indⱼ (wfEqTerm (soundness~↓! t)) ind∈))) P Q (<<-trans (<=-help-id-cong {a = sizeConv↑ P} {b = sizeConv↑ Q}) size)})
      (λ {PE.refl PE.refl → dec~↓! Γ≡Δ t u (<<-trans (<=-help-b'c' {a = sizeConv↑ P} {b = sizeConv↑ Q}) size)})
      (λ {PE.refl PE.refl p → decConv↑TermAll Γ≡Δ (indRectBranchTyListEq ind∈ (soundnessConv↑ p)) ms ns (<<-trans (<=-help-b''c'' {a = sizeConv↑ P} {b = sizeConv↑ Q}) size)})

  dec~↑! Γ≡Δ (cast-neInd A t eIndA _) (cast-neInd B u eIndB _) (leS size) =
    dec-castneInd-castneInd Γ≡Δ A t eIndA B u eIndB
                        (dec~↓! Γ≡Δ A B (<<-trans (<=-help-ab' {a = size~↓! A} {b = size~↓! B}) size))
                        (λ (_ , _ , AB) → decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A B AB u) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (sizeConv↑Term t)) (convert~size Γ≡Δ A B AB u)))
                                                                                               (<=-help-ab'' {a = size~↓! A} {c = size~↓! B} )) size))

  dec~↑! Γ≡Δ (cast-Ind A t eIndA _) (cast-Ind B u eIndB _) (leS size) =
    dec-castInd-castInd Γ≡Δ A t eIndA B u eIndB
                    (dec~↓! (symConEq Γ≡Δ) (sym~↓!U B) (sym~↓!U A) (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize B) (sym~↓!Usize A))
                                                                      (+-sym (size~↓! B) (size~↓! A))) ) (<=-help-ab' {a = size~↓! A} {b = size~↓! B}))) size))
                    (λ {PE.refl → decConv↑Term Γ≡Δ t u (<<-trans (<=-help-ab'' {a = size~↓! A} {c = size~↓! B}) size)})

  dec~↑! Γ≡Δ (cast-IndΠ Π t eIndΠ _) (cast-IndΠ Π′ u eIndΠ′ _) (leS size) =
    dec-castIndΠ-castIndΠ Γ≡Δ t eIndΠ u eIndΠ′
                      (decConv↑Term Γ≡Δ Π Π′ (<<-trans (<=-help-ab' {a = sizeConv↑Term Π}) size))
                      (λ {PE.refl → decConv↑Term Γ≡Δ t u (<<-trans (<=-help-ab'' {a = sizeConv↑Term Π} {c = sizeConv↑Term Π′}) size)})

  dec~↑! Γ≡Δ (cast-ΠInd Π t eΠInd _) (cast-ΠInd Π′ u eΠInd′ _) (leS size) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in dec-castΠInd-castΠInd Γ≡Δ t eΠInd u eΠInd′
                      (decConv↑Term (symConEq Γ≡Δ) (symConv↑Term (reflConEq ⊢Δ) Π′) (symConv↑Term (reflConEq ⊢Γ) Π)
                                              (<<-trans ((<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (size-symConv↑Term (reflConEq ⊢Δ) Π′) (size-symConv↑Term (reflConEq ⊢Γ) Π))
                                                                      (+-sym (sizeConv↑Term Π′) (sizeConv↑Term Π)))) (<=-help-ab' {a = sizeConv↑Term Π}))) size))
                      (λ ΠΠ′ → decConv↑TermConv Γ≡Δ (sym (stabilityEq (symConEq Γ≡Δ) (univ (soundnessConv↑Term ΠΠ′)))) t u
                                                 (<<-trans (<=-help-ab'' {a = sizeConv↑Term Π} {c = sizeConv↑Term Π′}) size))



  dec~↑! Γ≡Δ (cast-IndInd i≢k t eIndInd _) (cast-IndInd _ u eIndInd′ _) (leS size) =
    dec-castIndInd-castIndInd Γ≡Δ i≢k t eIndInd u eIndInd′
                              (λ {PE.refl → decConv↑Term Γ≡Δ t u (<<-trans (<=-help-ab1' {a = sizeConv↑Term t}) size)})

  dec~↑! Γ≡Δ (IndRect-cong y₁ y₂ y₃ y₄) (cast-cong A B ne≡1 ⊢e ⊢e') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (IndRect-cong y₁ y₂ y₃ y₄) + size~↑! (cast-cong A B ne≡1 ⊢e ⊢e')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = IndRect-cong y₁ y₂ y₃ y₄
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (IndRect-cong y₁ y₂ y₃ y₄) (cast-refl A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (IndRect-cong y₁ y₂ y₃ y₄) + size~↑! (cast-refl A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = IndRect-cong y₁ y₂ y₃ y₄
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                       (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (IndRect-cong y₁ y₂ y₃ y₄) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 ⊢e ⊢e') + size~↑! (IndRect-cong y₁ y₂ y₃ y₄)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = IndRect-cong y₁ y₂ y₃ y₄
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (IndRect-cong y₁ y₂ y₃ y₄) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (IndRect-cong y₁ y₂ y₃ y₄)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = IndRect-cong y₁ y₂ y₃ y₄
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ _ _ → ≢cast _) (≢cast _)
    ) size
  dec~↑! Γ≡Δ (cast-neInd y₁ y₂ y₃ y₄) (cast-cong A B ne≡1 ⊢e ⊢e') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-neInd y₁ y₂ y₃ y₄) + size~↑! (cast-cong A B ne≡1 ⊢e ⊢e')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-neInd y₁ y₂ y₃ y₄
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeInd (PE.subst Neutral (PE.sym eB) neB))
                       (λ e →   let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! y₁
                              in noNeInd (PE.subst Neutral eA neA))
    ) size
  dec~↑! Γ≡Δ (cast-neInd y₁ y₂ y₃ y₄) (cast-refl A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-neInd y₁ y₂ y₃ y₄) + size~↑! (cast-refl A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-neInd y₁ y₂ y₃ y₄
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                       (λ neA neB e → let _ , _ , eB , _ = cast-PE-injectivity e in noNeInd (PE.subst Neutral (PE.sym eB) neB))
                       (λ e →   let _ , eA , _ = cast-PE-injectivity e
                                    _ , neA , _ = ne~↓! y₁
                              in noNeInd (PE.subst Neutral eA neA))
    ) size
  dec~↑! Γ≡Δ (cast-cong A B _ _ _) (cast-neInd y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl B _ _) (cast-neInd y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-Ind y₁ y₂ y₃ y₄) (cast-cong A B ne≡1 ⊢e ⊢e') (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-Ind y₁ y₂ y₃ y₄) + size~↑! (cast-cong A B ne≡1 ⊢e ⊢e')) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-Ind y₁ y₂ y₃ y₄
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeInd (PE.subst Neutral (PE.sym eA) neA))
                       (λ e →   let _ , _ , eB , _ = cast-PE-injectivity e
                                    _ , _ , neB = ne~↓! y₁
                              in noNeInd (PE.subst Neutral eB neB))
    ) size
  dec~↑! Γ≡Δ (cast-Ind y₁ y₂ y₃ y₄) (cast-refl A~A ne≡1 ⊢e) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-Ind y₁ y₂ y₃ y₄) + size~↑! (cast-refl A~A ne≡1 ⊢e)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-Ind y₁ y₂ y₃ y₄
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                       (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeInd (PE.subst Neutral (PE.sym eA) neA))
                       (λ e →   let _ , _ , eB , _ = cast-PE-injectivity e
                                    _ , _ , neB = ne~↓! y₁
                              in noNeInd (PE.subst Neutral eB neB))
    ) size
  dec~↑! Γ≡Δ (cast-cong A B ne≡1 ⊢e ⊢e') (cast-Ind y₁ y₂ y₃ y₄) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-cong A B ne≡1 ⊢e ⊢e') + size~↑! (cast-Ind y₁ y₂ y₃ y₄)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-Ind y₁ y₂ y₃ y₄
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeInd (PE.subst Neutral (PE.sym eA) neA))
                      (λ e →   let _ , _ , eB , _ = cast-PE-injectivity e
                                   _ , _ , neB = ne~↓! y₁
                              in noNeInd (PE.subst Neutral eB neB))
    ) size
  dec~↑! Γ≡Δ (cast-refl A~B ne≡1 ⊢e) (cast-Ind y₁ y₂ y₃ y₄) (leS size) =
    neInsElim (λ ne≡1 → (size~↑! (cast-refl A~B ne≡1 ⊢e) + size~↑! (cast-Ind y₁ y₂ y₃ y₄)) <= _ → Dec _) (proj₁ (proj₂ (ne~↓! A~B))) ne≡1 (λ x x₁ x₂ A₁ D₁ whnfB k~l size →
    let X = cast-Ind y₁ y₂ y₃ y₄
        _ , neA , neB = ne~↓! A~B
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-refl-dec neA neB ⊢A x ⊢e
                     (yes (_ , _ , A~B))
                     (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A~B}) size))
                     (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeInd (PE.subst Neutral (PE.sym eA) neA))
                     (λ e →   let _ , _ , eB , _ = cast-PE-injectivity e
                                  _ , _ , neB = ne~↓! y₁
                              in noNeInd (PE.subst Neutral eB neB))
    ) size
  dec~↑! Γ≡Δ (cast-IndΠ y₁ y₂ y₃ y₄) (cast-cong A B _ _ _) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-IndΠ y₁ y₂ y₃ y₄) (cast-refl B _ _) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-cong A B _ _ _) (cast-IndΠ y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl B _ _) (cast-IndΠ y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ΠInd y₁ y₂ y₃ y₄) (cast-cong A B _ _ _) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠInd y₁ y₂ y₃ y₄) (cast-refl B _ _) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-cong A B _ _ _) (cast-ΠInd y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl B _ _) (cast-ΠInd y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-IndInd y₁ y₂ y₃ y₄) (cast-cong A B _ _ _) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-IndInd y₁ y₂ y₃ y₄) (cast-refl B _ _) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-cong A B _ _ _) (cast-IndInd y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-refl B _ _) (cast-IndInd y₁ y₂ y₃ y₄) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in Ind≢ne! neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (var-refl x₁ x₂) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (var-refl x₁ x₂) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (var-refl x₁ x₂) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (var-refl x₁ x₂) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (var-refl x₁ x₂) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (var-refl x₁ x₂) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (var-refl x₁ x₂) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (var-refl x₁ x₂) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (var-refl x₁ x₂) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (var-refl x₁ x₂) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (var-refl x₁ x₂) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (var-refl x₁ x₂) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x₁ x₂) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (app-cong x₁ x₂) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x₁ x₂) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (app-cong x₁ x₂) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x₁ x₂) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (app-cong x₁ x₂) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x₁ x₂) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (app-cong x₁ x₂) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x₁ x₂) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (app-cong x₁ x₂) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (app-cong x₁ x₂) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (app-cong x₁ x₂) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (var-refl y₁ y₂) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (var-refl y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (app-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (app-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (IndRect-cong x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Π x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (var-refl y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (var-refl y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (app-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (app-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-neInd x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (var-refl y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (var-refl y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (app-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (app-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-Ind x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (var-refl y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (var-refl y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (app-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (app-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndΠ x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (var-refl y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (var-refl y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (app-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (app-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-ΠInd x₁ x₂ x₃ x₄) (cast-IndInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (var-refl y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (var-refl y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (app-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (app-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (IndRect-cong y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (Emptyrec-cong y₁ y₂) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-neΠ y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-Π y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-ΠΠ%! y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-ΠΠ!% y₁ y₂ y₃ y₄ y₅) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-neInd y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-Ind y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-IndΠ y₁ y₂ y₃ y₄) PE.refl
  dec~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) _ = not-diag~↑! Γ≡Δ (cast-IndInd x₁ x₂ x₃ x₄) (cast-ΠInd y₁ y₂ y₃ y₄) PE.refl

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓! : ∀ {n k k' l l' R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → (e : Γ ⊢ k ~ k' ↓! R ^ lR)
        → (e' : Δ ⊢ l ~ l' ↓! T ^ lT)
        → (size~↓! e + size~↓! e') << n
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↓! A ^ lA)

  dec~↓! {n = 0} _ _ _ ()
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) (leS size)
        with dec~↑! Γ≡Δ k~l k~l₁ (<<-trans <=-help-ab1' size)
  ... | yes (B , lB , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑! k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , _ , [~] B (red D′) whnfC k~l₂)
  ... | no ¬p =
    no (λ { (A₂ , _ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , _ , k~l₂) })


  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {n A A' B B' r Γ Δ}
           → ⊢ Γ ≡ Δ
           → (e : Γ ⊢ A [conv↑] A' ^ r)
           → (e' : Δ ⊢ B [conv↑] B' ^ r)
           → (sizeConv↑ e + sizeConv↑ e') << n
           → Dec (Γ ⊢ A [conv↑] B ^ r)

  decConv↑ {n = 0} _ _ _ ()
  decConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) (leS size)
           with decConv↓ Γ≡Δ A′<>B′ A′<>B″ (<=-trans (<=-help-ab1' {a = 1+ (sizeConv↓ A′<>B′)}) size)
  ... | yes p =
    yes ([↑] A′ A″ D (stabilityRed* (symConEq Γ≡Δ) D₁) whnfA′ whnfA″ p)
  decConv↑ {r = r} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) (leS size) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ whnfA‴ whnfB‴ A′<>B‴) →
        let A‴≡B′  = whrDet* (D₂ , whnfA‴) (D , whnfA′)
            B‴≡B″ = whrDet* (D‴ , whnfB‴)
                                (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfA″)
        in  ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y ^ r) A‴≡B′ B‴≡B″ A′<>B‴) })


  decConv↓ : ∀ {n A A' B B' r Γ Δ}
           → ⊢ Γ ≡ Δ
           → (e : Γ ⊢ A [conv↓] A' ^ r)
           → (e' : Δ ⊢ B [conv↓] B' ^ r)
           → (sizeConv↓ e + sizeConv↓ e') << n
           → Dec (Γ ⊢ A [conv↓] B ^ r)

  decConv↓ {n = 0} _ _ _ ()
  decConv↓ Γ≡Δ (U-refl {r = r} x x₁) (U-refl {r = r′} x₂ x₃) (leS size) with dec-relevance r r′
  ... | yes p = yes (U-refl p x₁)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (soundnessConv↓ p)))
  decConv↓ Γ≡Δ (univ x) (univ x₁) (leS size) with decConv↓Term Γ≡Δ x x₁ (<=-trans (<=-help-ab1' {a = sizeConv↓ (univ x)}) size)
  ... | yes p = yes (univ p)
  ... | no ¬p = no (λ { (univ x) → ¬p x })


  -- Decidability of algorithmic equality of terms.

  decConv↑Term : ∀ {n t t' u u' A Γ Δ l}
               → ⊢ Γ ≡ Δ
               → (e : Γ ⊢ t [conv↑] t' ∷ A ^ l)
               → (e' : Δ ⊢ u [conv↑] u' ∷ A ^ l)
               → (sizeConv↑Term e + sizeConv↑Term e') << n
               → Dec (Γ ⊢ t [conv↑] u ∷ A ^ l)


  decConv↑Term {n = 0} _ _ _ ()
  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁) (leS size)
               rewrite whrDet* (D , whnfB) (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfB₁)
               with decConv↓Term Γ≡Δ t<>u t<>u₁ (<=-trans (<=-help-ab1' {a = 1+ (sizeConv↓Term t<>u)}) size)
  ... | yes p =
    let Δ≡Γ = symConEq Γ≡Δ
    in  yes ([↑]ₜ B₁ t′ t″ (stabilityRed* Δ≡Γ D₁)
                  d (stabilityRed*Term Δ≡Γ d₁) whnfB₁ whnft′ whnft″ p)
  ... | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ whnfB₂ whnft‴ whnfu‴ t<>u₂) →
        let B₂≡B₁ = whrDet* (D₂ , whnfB₂)
                             (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfB₁)
            t‴≡u′ = whrDet*Term (d₂ , whnft‴)
                              (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ^ _) (PE.sym B₂≡B₁) d
                              , whnft′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴)
                               (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ^ _)
                                         (PE.sym B₂≡B₁)
                                         (stabilityRed*Term (symConEq Γ≡Δ) d₁)
                               , whnft″)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z ^ _)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂) })

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {n t t' u u' A Γ Δ l}
               → ⊢ Γ ≡ Δ
               → (e : Γ ⊢ t [conv↓] t' ∷ A ^ l)
               → (e' : Δ ⊢ u [conv↓] u' ∷ A ^ l)
               → (sizeConv↓Term e + sizeConv↓Term e') << n
               → Dec (Γ ⊢ t [conv↓] u ∷ A ^ l)

  decConv↓Term {n = 0} _ _ _ ()

  decConv↓Term Γ≡Δ (U-refl {r = r} _ x) (U-refl {r = r′} _ x₁) (leS size)
    with dec-relevance r r′
  ... | yes p = yes (U-refl p x)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (univ (soundnessConv↓Term p))))

  decConv↓Term Γ≡Δ (ne K) (ne K₁) (leS size)
    with dec~↓! Γ≡Δ K K₁ (<=-trans (<=-help-ab1' {a = 1+ (size~↓! K)}) size)
  ... | yes (A , lA , K~K₁) = yes (ne (~atU' K (A , lA , K~K₁)))
  ... | no ¬p = no (λ x → ¬p (Univ _ _ , _ , decConv↓Term-U-ins x K))


  decConv↓Term Γ≡Δ (Empty-refl x₁) (Empty-refl x₃) _ = yes (Empty-refl x₁)

  decConv↓Term Γ≡Δ (Ind-refl {i} x i∈) (Ind-refl {j} x₁ _) _ with i ≟ j
  ... | yes PE.refl = yes (Ind-refl x i∈)
  ... | no ¬p = no λ { (Ind-refl _ _) → ¬p PE.refl ; (ne ()) ; (ne-ins _ x₁ () x₃) }

  decConv↓Term Γ≡Δ (Π-cong {rF = rF} {lF = lF} {lG = lG} {lΠ = l} l≡ PE.refl PE.refl PE.refl lF< lG< ⊢F F G)
    (Π-cong {rF = rH} {lF = lH} {lG = lE} {lΠ = l′} l′≡ PE.refl PE.refl PE.refl _ _ ⊢H H E) (leS size)
    with dec-relevance rF rH | dec-level lF lH | dec-level lG lE | dec-level l l′
  ... | yes PE.refl | yes PE.refl | yes PE.refl | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p PE.refl ; (ne ()) ; (ne-ins _ _ () _) }
  ... | yes PE.refl | yes PE.refl | no ¬p | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₃ ; (ne ()) ; (ne-ins _ _ () _) }
  ... | yes PE.refl | no ¬p | _ | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₂ ; (ne ()) ; (ne-ins _ _ () _) }
  ... | no ¬p | _ | _ | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₁ ; (ne ()) ; (ne-ins _ _ () _) }
  ... | yes PE.refl | yes PE.refl | yes PE.refl | yes PE.refl
    with decConv↑Term Γ≡Δ F H (<=-trans (leS (<=-help-ab' {a = sizeConv↑Term F})) size)
  ... | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₇ ; (ne ()) ; (ne-ins _ _ () _) }
  ... | yes pFH
    with decConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term pFH)) G E (<=-trans (leS (<=-help-ab'' {a = sizeConv↑Term F} {c = sizeConv↑Term H})) size)
  ... | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₈ ; (ne ()) ; (ne-ins _ _ () _) }
  ... | yes pGE = yes (Π-cong l≡ PE.refl PE.refl PE.refl lF< lG< ⊢F pFH pGE)

  decConv↓Term Γ≡Δ (Id-cong {l} A t u) (Id-cong {l'} B t' u') (leS size)
    with dec-level l l'
  ... | no ¬p = no λ { (ne ()) ; (ne-ins _ _ () _) ; (Id-cong x₁ x₂ x₃) →
        let _ , ⊢A₁ , ⊢A₂ = syntacticEqTerm (soundnessConv↑Term x₁)
            _ , ⊢A₁' , _ = syntacticEqTerm (soundnessConv↑Term A)
            _ , ⊢A₂' , _ = syntacticEqTerm (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) B))
            el , _ = type-uniq ⊢A₁ ⊢A₁'
            el' , _ = type-uniq ⊢A₂ ⊢A₂'
        in ¬p (PE.trans (PE.sym (next-inj el)) (next-inj el')) }
  ... | yes PE.refl 
    with decConv↑Term Γ≡Δ A B (<<-trans (<=-help-id-cong {a =  sizeConv↑Term A}) size)
  ... | no ¬p = no λ { (ne ()) ; (ne-ins _ _ () _) ; (Id-cong x₁ x₂ x₃) →
        let _ , ⊢A₁ , ⊢A₂ = syntacticEqTerm (soundnessConv↑Term x₁)
            _ , ⊢A₁' , _ = syntacticEqTerm (soundnessConv↑Term A)
            el , _ = type-uniq ⊢A₁ ⊢A₁'
        in ¬p (PE.subst (λ ll → _ ⊢ _  [conv↑] _ ∷ U ll ^ next ll ) (next-inj el) x₁) }
  ... | yes A~B
    with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term A~B)) t t' 
                          (<<-trans (<=-trans (<=-cong-+ (le-refl (sizeConv↑Term t))
                                    (≡-to-<= PE.refl))
                                    (<=-help-b'c' {a = sizeConv↑Term A} {b = sizeConv↑Term B})) size)
  ... | no ¬p = no λ { (ne ()) ; (ne-ins _ _ () _) ; (Id-cong x₁ x₂ x₃) →
        let _ , ⊢A₁ , ⊢A₂ = syntacticEqTerm (soundnessConv↑Term x₁)
            _ , ⊢A₁' , _ = syntacticEqTerm (soundnessConv↑Term A)
            el , _ = type-uniq ⊢A₁ ⊢A₁'
        in ¬p (PE.subst (λ ll → _ ⊢ _  [conv↑] _ ∷ _ ^ ι ll ) (next-inj el) x₂) }
  ... | yes t~t' 
    with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term A~B)) u u'
                            (<<-trans (<=-trans (<=-cong-+ (le-refl (sizeConv↑Term u))
                                                (≡-to-<= PE.refl))
                                                (<=-help-b''c'' {a = sizeConv↑Term A} {b = sizeConv↑Term B})) size) 
  ... | no ¬p = no λ { (ne ()) ; (ne-ins _ _ () _) ; (Id-cong x₁ x₂ x₃) →
        let _ , ⊢A₁ , ⊢A₂ = syntacticEqTerm (soundnessConv↑Term x₁)
            _ , ⊢A₂' , _ = syntacticEqTerm (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) B))
            el , _ = type-uniq ⊢A₂ ⊢A₂'
        in ¬p (PE.subst (λ ll → _ ⊢ _  [conv↑] _ ∷ _ ^ ι ll ) (next-inj el) x₃) }
  ... | yes u~u' = yes (Id-cong A~B t~t' u~u')


  decConv↓Term Γ≡Δ (Ind-ins K) (Ind-ins K₁) (leS size)
    with dec~↓! Γ≡Δ K K₁ (<=-trans (<=-help-ab1' {a = 1+ (size~↓! K)}) size)
  ... | yes p = yes (Ind-ins (let _ , ⊢k , _ = syntacticEqTerm (soundness~↓! K) in ~atInd ⊢k p))
  ... | no ¬p = no λ x → ¬p (Ind _ , _ , decConv↓Term-Ind-ins x K)

  decConv↓Term Γ≡Δ (ne-ins ⊢k _ neA k) (ne-ins ⊢k₁ _ _ k₁) (leS size)
    with dec~↓! Γ≡Δ k k₁ (<=-trans (<=-help-ab1' {a = 1+ (size~↓! k)}) size)
  ... | yes (B , lB , k~k₁) =
    let whnfB , neK , neK₁ = ne~↓! k~k₁
        _ , ⊢k∷B , _ = syntacticEqTerm (soundness~↓! k~k₁)
        l≡l , ⊢A≡B = neTypeEq neK ⊢k∷B ⊢k
    in yes (ne-ins ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₁) neA (PE.subst (λ X → _ ⊢ _ ~ _ ↓! _ ^ X) l≡l k~k₁))
  ... | no ¬p = no λ x → ¬p (decConv↓Term-ne-ins neA x)



  decConv↓Term Γ≡Δ (η-eq lF< lG< ⊢F ⊢f _ funf _ f) (η-eq _ _ _ ⊢g _ fung _ g) (leS size)
    with decConv↑Term (Γ≡Δ ∙ refl ⊢F) f g (<=-trans (<=-help-ab1' {a = 1+ (sizeConv↑Term f)}) size)
  ... | yes p = yes (η-eq lF< lG< ⊢F ⊢f (stabilityTerm (symConEq Γ≡Δ) ⊢g) funf fung p)
  ... | no ¬p = no (λ { (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) → ¬p x₇ ; (ne-ins _ _ () _) })

  -- ctr uses a map-spine: dual ctr-cong matching does not unify, so we
  -- generalize the type of the second derivation (cf. transConv↓Term).
  decConv↓Term {n = 1+ n} {Γ = Γ} {Δ = Δ} Γ≡Δ (ctr-cong {ind = ind} {j = j} {args = args} ⊢Γ ind∈ argsTy ps) e' (leS size) =
    go e' PE.refl size
    where
    go : ∀ {i' u u'} (e2 : Δ ⊢ u [conv↓] u' ∷ Ind i' ^ ι ⁰)
       → i' PE.≡ SI.SInd.name ind
       → (sizeConv↓Term (ctr-cong ⊢Γ ind∈ argsTy ps) + sizeConv↓Term e2) <= n
       → Dec (Γ ⊢ ctr (SI.SInd.name ind) j args [conv↓] u ∷ Ind (SI.SInd.name ind) ^ ι ⁰)
    go (ne-ins _ _ () _) _ _
    go (Ind-ins x) _ _ = no (λ p → ctr-ne-inv p PE.refl (proj₁ (proj₂ (ne~↓! x))))
    go (ctr-cong {j = j₂} ⊢Γ₂ ind∈₂ argsTy₂ qs) eq fuel
      with SI.name-inj senv (proj₁ swf) ind∈₂ ind∈ eq
    ... | PE.refl with j ≟ j₂
    ... | no ¬p = no (λ p → ¬p (proj₁ (ctr-inv ind∈ argsTy p PE.refl PE.refl)))
    ... | yes PE.refl with PE.trans (PE.sym argsTy) argsTy₂
    ... | PE.refl with decConv↑TermAll Γ≡Δ (reflAll₂ ps) ps qs
                         (<=-trans (<=-help-rigid1 {a = sizeConv↑TermAll ps} {b = sizeConv↑TermAll qs}) fuel)
    ... | yes rs = yes (ctr-cong ⊢Γ ind∈ argsTy rs)
    ... | no ¬rs = no (λ p → ¬rs (proj₂ (ctr-inv ind∈ argsTy p PE.refl PE.refl)))

  decConv↓Term Γ≡Δ (U-refl x x₁) (ne x₂) _ =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₂ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (U-refl x x₁) (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) _ = no λ { (ne ()) }
  decConv↓Term Γ≡Δ (ne x) (U-refl x₁ x₂) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (Empty-refl x₂) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB (cast-refl x' x₁' x₂')) → ⁰-next x₁ }))
  decConv↓Term Γ≡Δ (ne x) (Id-cong x₂ x₃ x₄) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Empty-refl x₁) (ne x₂) _ =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₂ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Empty-refl x₁) (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) _ = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Empty-refl x₁) (Id-cong x₃ x₄ x₅) _ = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (U-refl x₈ x₉) _ = no λ { (ne ()) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne x₈) _ =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₈ (λ { ([~] A D whnfB (cast-refl x x₁ x₂)) → ⁰-next l }))
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Empty-refl x₉) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Id-cong x₉ x₁₀ x₁₁) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Id-cong x x₁ x₂) (ne x₃) _ =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₃ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Id-cong x x₁ x₂) (Empty-refl x₄) _ = no λ { (ne ()) ; (ne-ins x x₁ () _) }
  decConv↓Term Γ≡Δ (Id-cong x x₁ x₂) (Π-cong x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ne x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Empty-refl x₅)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Id-cong x₅ x₆ x₇)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (η-eq x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁)
  decConv↓Term Γ≡Δ (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne-ins x₈ x₉ () x₁₁)
  decConv↓Term Γ≡Δ (ne x) (Ind-refl x₁ _) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Ind-refl x _) (ne x₁) _ =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Ind-refl x _) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) _ = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Ind-refl x₈ _) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Ind-refl x₄ _)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Ind-ins x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ctr-cong x₄ x₅ x₆ x₇)
  decConv↓Term Γ≡Δ (Ind-ins x) (ctr-cong x₁ x₂ x₃ x₄) _ =
    no (λ p → ctr-ne-inv (symConv↓Term Γ≡Δ p) PE.refl (proj₁ (proj₂ (ne~↓! x))))



  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {n t t' u u' A B r Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ r
                → (e : Γ ⊢ t [genconv↑] t' ∷ A ^ r)
                → (e' : Δ ⊢ u [genconv↑] u' ∷ B ^ r)
                → (size[genconv↑] e + size[genconv↑] e') << n
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ r)
  decConv↑TermConv {r = [ ! , l ]} Γ≡Δ A≡B t u size =
    decConv↑TermConv! Γ≡Δ (stabilityEq Γ≡Δ (sym A≡B)) t u size
  decConv↑TermConv {r = [ % , l ]} Γ≡Δ A≡B (%~↑ ⊢t ⊢t') (%~↑ ⊢u ⊢u') _ =
    yes (%~↑ ⊢t (conv (stabilityTerm (symConEq Γ≡Δ) ⊢u) (sym A≡B)))

  -- The conversion proof B≡A is a variable here on purpose: with the
  -- concrete proof (stabilityEq Γ≡Δ (sym A≡B)) inlined, checking the size
  -- argument makes Agda evaluate that proof term, which takes minutes.
  decConv↑TermConv! : ∀ {n t t' u u' A B Γ Δ l}
                → ⊢ Γ ≡ Δ
                → Δ ⊢ B ≡ A ^ [ ! , l ]
                → (e : Γ ⊢ t [conv↑] t' ∷ A ^ l)
                → (e' : Δ ⊢ u [conv↑] u' ∷ B ^ l)
                → (sizeConv↑Term e + sizeConv↑Term e') << n
                → Dec (Γ ⊢ t [conv↑] u ∷ A ^ l)
  decConv↑TermConv! Γ≡Δ B≡A t u size =
    decConv↑Term Γ≡Δ t (convConvTerm u B≡A) (<<-trans (<=-cong-+ (le-refl (sizeConv↑Term t)) (≡-to-<= (convConv↑TermSize (reflConEq (wfEq B≡A)) B≡A u))) size)

  decConv↑TermConv′ : ∀ {n t t' u u' A B r r₁ r₂ Γ Δ}
                → ⊢ Γ ≡ Δ
                → r PE.≡ r₁
                → r PE.≡ r₂
                → Γ ⊢ A ≡ B ^ r
                → (e : Γ ⊢ t [genconv↑] t' ∷ A ^ r₁)
                → (e' : Δ ⊢ u [genconv↑] u' ∷ B ^ r₂)
                → (size[genconv↑] e + size[genconv↑] e') << n
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ r)
  decConv↑TermConv′ Γ≡Δ PE.refl PE.refl A≡B t u size = decConv↑TermConv Γ≡Δ A≡B t u size


  -- Decidability of algorithmic equality of lists of terms (branches of IndRect,
  -- arguments of constructors), pointwise at equal types.
  decConv↑TermAll : ∀ {n ms ms' ns ns' As Bs Γ Δ l}
                  → ⊢ Γ ≡ Δ
                  → All₂ (λ A B → Γ ⊢ A ≡ B ^ [ ! , l ]) As Bs
                  → (ps : All₃ (λ a a' A → Γ ⊢ a [conv↑] a' ∷ A ^ l) ms ms' As)
                  → (qs : All₃ (λ a a' A → Δ ⊢ a [conv↑] a' ∷ A ^ l) ns ns' Bs)
                  → (sizeConv↑TermAll ps + sizeConv↑TermAll qs) << n
                  → Dec (All₃ (λ a a' A → Γ ⊢ a [conv↑] a' ∷ A ^ l) ms ns As)
  decConv↑TermAll Γ≡Δ []ₐ []ₐ []ₐ _ = yes []ₐ
  decConv↑TermAll Γ≡Δ (A≡B ∷ₐ eqs) (p ∷ₐ ps) (q ∷ₐ qs) fuel =
    dec∷ₐ (decConv↑TermConv Γ≡Δ A≡B p q
             (<<-trans (<=-help-All-hd {a = sizeConv↑Term p} {b = sizeConv↑TermAll ps}
                                       {c = sizeConv↑Term q} {d = sizeConv↑TermAll qs}) fuel))
          (decConv↑TermAll Γ≡Δ eqs ps qs
             (<<-trans (<=-help-All-tl {a = sizeConv↑Term p} {b = sizeConv↑TermAll ps}
                                       {c = sizeConv↑Term q} {d = sizeConv↑TermAll qs}) fuel))
