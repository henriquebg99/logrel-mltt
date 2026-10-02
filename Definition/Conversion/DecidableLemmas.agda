{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Conversion.DecidableLemmas (senv : SI.SEnv) (swf : SI.swfenv senv) (equivs : E.Equivs senv) where
open import Definition.Untyped senv equivs
open import Definition.Untyped.Properties senv equivs
open import Definition.Typed senv equivs as T
open import Definition.Typed.Properties senv swf equivs
open import Definition.Conversion senv equivs
open import Definition.Conversion.Whnf senv swf equivs
open import Definition.Conversion.Soundness senv swf equivs
open import Definition.Conversion.Symmetry senv swf equivs
open import Definition.Conversion.Transitivity senv swf equivs
open import Definition.Conversion.SymmetrySize senv swf equivs
open import Definition.Conversion.Stability senv swf equivs
open import Definition.Conversion.Conversion senv swf equivs
open import Definition.Conversion.Lift senv swf equivs
open import Definition.Conversion.Inversion senv swf equivs
open import Definition.Conversion.ConvSize senv equivs
open import Definition.Conversion.ConversionProp senv swf equivs
open import Definition.Typed.Consequences.Syntactic senv swf equivs
open import Definition.Typed.Consequences.Substitution senv swf equivs
open import Definition.Typed.Consequences.Injectivity senv swf equivs
open import Definition.Typed.Consequences.Reduction senv swf equivs
open import Definition.Typed.Consequences.Equality senv swf equivs
open import Definition.Typed.Consequences.Inequality senv swf equivs as IE
open import Definition.Typed.Consequences.NeTypeEq senv swf equivs
open import Definition.Typed.Consequences.Inversion senv swf equivs
open import Definition.Typed.Consequences.TypeUnicity senv swf equivs
open import Definition.Conversion.Consequences.Completeness senv swf equivs
open import Definition.Conversion.EqRelInstance senv swf equivs
open import Definition.Conversion.HelperDecidable senv swf equivs
open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary hiding (map)
open import Tools.List using (All₂; All₃; []ₐ; _∷ₐ_; map; _∈ₗ_)
open import Tools.Maybe using (just)
import Tools.PropositionalEquality as PE
abstract
  ~atU' : ∀ {Γ t v u r lU l}
    → Γ ⊢ t ~ v ↓! Univ r lU ^ l
    → (∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → Γ ⊢ t ~ u ↓! Univ r lU ^ l
  ~atU' t~v t~u = let _ , ⊢t , _ = syntacticEqTerm (soundness~↓! t~v) in ~atU ⊢t t~u

  ~atU-' : ∀ {Γ t v u r lU l}
    → Γ ⊢ v ~ t ↓! Univ r lU ^ l
    → (∃ λ A → ∃ λ lA → Γ ⊢ u ~ t ↓! A ^ lA)
    → Γ ⊢ u ~ t ↓! Univ r lU ^ l
  ~atU-' v~t u~t = let _ , _ , ⊢t = syntacticEqTerm (soundness~↓! v~t) in ~atU- ⊢t u~t

  sym~↓!U : ∀ {Γ A B r lU l}
    → Γ ⊢ A ~ B ↓! Univ r lU ^ l
    → Γ ⊢ B ~ A ↓! Univ r lU ^ l
  sym~↓!U A~B = let _ , _ , ⊢B = syntacticEqTerm (soundness~↓! A~B)
                    _ , _ , _ , B~A = sym~↓! (reflConEq (wfTerm ⊢B)) A~B
                in ~atU ⊢B (_ , _ , B~A)

  sym~↓!Usize : ∀ {Γ A B r lU l}
    → (A~B : Γ ⊢ A ~ B ↓! Univ r lU ^ l)
    → size~↓! (sym~↓!U A~B) PE.≡ size~↓! A~B
  sym~↓!Usize A~B =
    let _ , _ , ⊢B = syntacticEqTerm (soundness~↓! A~B)
        _ , _ , _ , B~A = sym~↓! (reflConEq (wfTerm ⊢B)) A~B
    in PE.trans (~atUsize ⊢B (_ , _ , B~A)) (size-sym~↓! (reflConEq (wfTerm ⊢B)) A~B)


abstract
  cast-refl-dec : ∀ {Γ A B t e u}
              → Neutral A
              → Neutral B
              → Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
              → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA)
  cast-refl-dec neA neB ⊢A ⊢tA ⊢e (yes (_ , _ , A~B)) (yes (_ , _ , p)) _ =
    let _ , neA , _ = ne~↓! A~B
        var≡t = soundness~↑! p
        ⊢K , ⊢t , ⊢u = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t ⊢tA
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K))
    in yes ( _ , _ , cast-refl (~atU ⊢A (_ , _ , A~B))
                               (ne-ins ⊢tA (conv (PE.subst (λ X → _ ⊢ _ ∷ _ ^ [ ! , X ]) el ⊢u )
                                               (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , X ]) el eA))
                                       neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)))
                                                                         ⊢e)
  cast-refl-dec neA neB ⊢A _ ⊢e (yes (_ , _ , A~B)) (no ¬p) noeqNe =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl x x₁ x₂) → ¬p (_ , _ , let _ , neA , _ = ne~↓! A~B
                                                          _ , var~t' , _ = [conv↓]ne neA x₁
                                                          _ , var~t = neutral↓↑ var~t'
                                                      in var~t) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) })
  cast-refl-dec neA neB ⊢A _ ⊢e (no ¬AB) _ noeqNe =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) })

abstract

  cast-refl'-dec : ∀ {Γ A B t e u}
                 → Neutral A
                 → Neutral B
                 → Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
                 → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A B e t ↑! U ^ lA)
  cast-refl'-dec neA neB ⊢B ⊢tA ⊢e (yes (_ , _ , B~A)) (yes (_ , _ , p)) _ =
    let _ , _ , neA = ne~↓! B~A
        var≡t = soundness~↑! p
        ⊢K , ⊢u , ⊢t  = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t ⊢tA
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K))
    in yes ( _ , _ , cast-refl' (~atU ⊢B (_ , _ , B~A))
                                (ne-ins (conv (PE.subst (λ X → _ ⊢ _ ∷ _ ^ [ ! , X ]) el ⊢u )
                                              (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , X ]) el eA))
                                        ⊢tA
                                        neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)))
                                        ⊢e)
  cast-refl'-dec neA neB _ _ ⊢e (yes (_ , _ , A~B)) (no ¬p) noeqNe =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' x x₁ x₂) → ¬p (_ , _ , let _ , _ , neA = ne~↓! A~B
                                                           _ , var~t' , _ = [conv↓]ne neA x₁
                                                           _ , var~t = neutral↓↑ var~t'
                                                       in var~t) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) })
  cast-refl'-dec neA neB _ _ ⊢e (no ¬AB) _ noeqNe =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' x x₁ x₂) → ¬AB (_ , _ , x) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) })

abstract

  cast-cast-≡ : ∀ {Γ A A' B B' t t' e e' X lX}
                 → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ A' B' e' t' ↑! X ^ lX
                 → Γ ⊢ B ≡ B' ^ [ ! , ι ⁰ ]
  cast-cast-≡ X =
    let cast≡cast = soundness~↑! X
        _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
        _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
        _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
        eqR , el = typeinfo-PE-injectivity eqR
        eqT , _ = typeinfo-PE-injectivity eqT
        T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
        R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
    in T.trans (T.sym R≡R') T≡T'


abstract

  castneΠ-refl'-dec : ∀ {Γ A X Y rX t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeΠ : ∀ {A' X' Y' rX' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' (Π X' ^ rX' ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ ! ) e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ) e t ~ u ↑! U ^ lA)
  castneΠ-refl'-dec _ noeqNe noeqNeΠ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neB , neA = ne~↓! x in noeqNe neA neB PE.refl ;
                                                    (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → let _ , _ , neA = ne~↓! x₁ in noeqNeΠ neA PE.refl } )

abstract

  cast-refl'-dec~ : ∀ {Γ A A' B B' t t' e u}
                 → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
                 → Γ ⊢ B ~ B' ↓! U ⁰ ^ ι ¹
                 → Γ ⊢ t [conv↓] t' ∷ A ^ ι ⁰
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A B e t ↑! U ^ lA)
  cast-refl'-dec~ A B t ⊢e decAB dectu noeqNe =
    let _ , neA , _ = ne~↓! A
        _ , neB , _ = ne~↓! B
        _ , ⊢B , _ = syntacticEqTerm (soundness~↓! B)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t)
    in cast-refl'-dec neA neB ⊢B ⊢t ⊢e decAB dectu noeqNe

  cast-refl-dec~ : ∀ {Γ A A' B B' t t' e u}
                 → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
                 → Γ ⊢ B ~ B' ↓! U ⁰ ^ ι ¹
                 → Γ ⊢ t [conv↓] t' ∷ A ^ ι ⁰
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA)
  cast-refl-dec~ A B t ⊢e decAB dectu noeqNe =
    let _ , neA , _ = ne~↓! A
        _ , neB , _ = ne~↓! B
        _ , ⊢A , _ = syntacticEqTerm (soundness~↓! A)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t)
    in cast-refl-dec neA neB ⊢A ⊢t ⊢e decAB dectu noeqNe

  castneΠ-refl'-dec~ : ∀ {Γ A A' X Y rX t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeΠ : ∀ {A' X' Y' rX' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' (Π X' ^ rX' ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ ! ) e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ) e t ~ u ↑! U ^ lA)
  castneΠ-refl'-dec~ A noeqNe noeqNeΠ = let _ , neA , _ = ne~↓! A in castneΠ-refl'-dec neA noeqNe noeqNeΠ

  cast-cast-dec : ∀ {Γ Δ A B t e C D u e'}
              → ⊢ Γ ≡ Δ
              → Neutral A
              → Neutral B
              → Neutral C
              → Neutral D
              → Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Δ ⊢ C ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Δ ⊢ D ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
              → Δ ⊢ u ∷ C ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
              → (⊢e' : Δ ⊢ e' ∷ (Id (U ⁰) C D) ^ [ % , ι ⁰ ])
              → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ C ↓! U ^ lA))
              → (decDB : Dec (∃ λ U → ∃ λ lA → Δ ⊢ D ~ B ↓! U ^ lA))
              → (decAC : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
              → (decCD : Dec (∃ λ U → ∃ λ lA → Δ ⊢ C ~ D ↓! U ^ lA))
              → (dectu : (∃ λ U → ∃ λ lA → Γ ⊢ A ~ C ↓! U ^ lA) → Dec (Γ ⊢ t [conv↓] u ∷ A ^ ι ⁰))
              → (dectcast : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ cast ⁰ C D e' u ↑! U ^ lA))
              → (deccastu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ C D e' u ↑! U ^ lA)
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' _ (no ¬BD) _ _ _ _ _ =
    no λ { (_ , _ , X) → ¬BD (U ⁰ , ι ¹ , ~atU ⊢D
                                               let T≡R = sym (cast-cast-≡ X)
                                                   eq = completeEqNeutral neD neB (un-univ≡ (stabilityEq Γ≡Δ T≡R))
                                               in  _ , _ , eq) } 
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' (yes (_ , _ , A~C)) (yes (_ , _ , B~D)) (yes (_ , _ , A~B)) _ dectu _ _
    with dectu (_ , _ , A~C)
  ... | yes p = yes (_ , _ , cast-cong (~atU ⊢A (_ , _ , A~C)) (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D)) p ⊢e (stabilityTerm (symConEq Γ≡Δ) ⊢e'))
  ... | no ¬p = no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                         cast≡cast = soundness~↑! X
                                         A≡B = soundness~↓! (~atU ⊢A (_ , _ , A~B))
                                         A≡C = soundness~↓! (~atU ⊢A (_ , _ , A~C))
                                         B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D (_ , _ , B~D))))
                                         C≡D = trans (sym (univ A≡C)) (trans (univ A≡B) (sym B≡D))
                                         _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                         _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                         eqR , el = typeinfo-PE-injectivity eqR
                                         R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                         cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                         ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                         net = castNeutralInv neA neB whnfcast
                                         neu = castNeutralInv neC neD whnfcast'                                        
                                     in ¬p (completeEqTerm↓ (ne neA) (ne net) (ne neu)
                                                            (trans (sym (conv (T.cast-refl A≡B ⊢e ⊢t') (sym (univ A≡B))))
                                                            (trans (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))
                                                            (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) ⊢e') (stabilityTerm (symConEq Γ≡Δ) ⊢u))
                                                                  (trans B≡D (sym (univ A≡B))))))) }
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (yes C~D) _ _ _ =
    no λ { (_ , _ , X) → ¬AC (let _ , _ , _ , D~B = sym~↓! (reflConEq (wfTerm eCD)) (~atU ⊢D B~D)
                                  _ , _ , A~D , _ = trans~↓!-simpl (~atU ⊢A A~B) (stability~↓! (symConEq Γ≡Δ) D~B)
                                  _ , _ , _ , D~C = sym~↓! (reflConEq (wfTerm eCD)) (~atU ⊢C C~D)
                                  _ , _ , A~C , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) D~C)
                              in _ , _ , A~C )}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (yes A~C) (yes B~D) (no ¬AB) (yes C~D) _ _ _ =
    no λ { (_ , _ , X) → ¬AB (let _ , _ , A~D , _ = trans~↓!-simpl (~atU ⊢A A~C) (stability~↓! (symConEq Γ≡Δ) (~atU ⊢C C~D))
                                  _ , _ , A~B , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) (~atU ⊢D B~D))
                              in _ , _ , A~B )}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (no ¬CD) _ _ _ =
    no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬AC (_ , _ , x) ;
           (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
           (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , x))
                                          in ¬CD (_ , _ , D~B)}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (no ¬CD) _ (yes (_ , _ , tu)) _ =
    yes (_ , _ , let t≡cast = soundness~↑! tu
                     ⊢K , _ , ⊢cast' = syntacticEqTerm t≡cast
                     _ , ⊢A' , ⊢B' , _ , ⊢t' , T≡T , eqT , _ = inversion-cast ⊢cast'
                     eqT , el = typeinfo-PE-injectivity eqT
                     _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                     A≡B = soundness~↓! (~atU ⊢A A~B)
                     B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                  in cast-refl (~atU ⊢A A~B) (ne-ins ⊢t (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A')
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B')
                                                                                                (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t'))
                                                                                       (trans B≡D (sym (univ A≡B))))
                                                                          neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                     eAB)

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (no ¬CD) _ (no ¬tu) _ =
                 no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          A≡B = soundness~↓! (~atU ⊢A A~B)
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neA (completeEqTerm↓ (ne neA) (ne net) (ne (castₙ neC neD neu))
                                                                                               (trans (sym (conv (T.cast-refl A≡B eAB ⊢t') (sym (univ A≡B)) ))
                                                                                                      (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) }

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (yes C~D) _ _ (yes (_ , _ , tu)) =
                           yes (_ , _ , let t≡cast = soundness~↑! tu
                                            ⊢K , ⊢cast , _ = syntacticEqTerm t≡cast
                                            _ , ⊢A' , ⊢B' , _ , ⊢t' , T≡T , eqT , _ = inversion-cast ⊢cast
                                            eqT , el = typeinfo-PE-injectivity eqT
                                            _ , _ , _ , D~C = sym~↓! (symConEq Γ≡Δ) (~atU ⊢C C~D)
                                            _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                                            C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢C C~D)))
                                            B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                            in cast-refl' (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , D~C))
                                                          (ne-ins (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A')
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B')
                                                                                 eAB
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t'))
                                                                        (trans (sym B≡D) (sym C≡D)))
                                                                  (stabilityTerm (symConEq Γ≡Δ) ⊢u)
                                                                  neC ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                          (stabilityTerm (symConEq Γ≡Δ) eCD))

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (yes C~D) _ _ (no ¬tu) =
                 no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢C C~D)))
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neB (completeEqTerm↓ (ne neB) (ne (castₙ neA neB net)) (ne neu)
                                                                                               (trans (conv cast≡cast' R≡R')
                                                                                                      (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                                         (stabilityTerm (symConEq Γ≡Δ) ⊢u))
                                                                                                            (trans (sym T≡T') R≡R'))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) } 

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' (yes (_ , _ , A~C)) (yes (_ , _ , B~D)) (no ¬AB) (no ¬CD) dectu _ _
    with dectu (_ , _ , A~C)
  ... | yes p = yes (_ , _ , cast-cong (~atU ⊢A (_ , _ , A~C)) (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D)) p ⊢e (stabilityTerm (symConEq Γ≡Δ) ⊢e'))
  ... | no ¬p = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬p x₂ ;
                       (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
                       (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , x))
                                                      in ¬CD (_ , _ , D~B) }

abstract

  dec-var-var : ∀ {Γ Δ A A' x y x' y' l l'}
              → ⊢ Γ ≡ Δ
              → (⊢x : Γ ⊢ var x ∷ A ^ [ ! , l ])
              → (e : x PE.≡ y)
              → (⊢x' : Δ ⊢ var x' ∷ A' ^ [ ! , l' ])
              → (e' : x' PE.≡ y')
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ var x ~ var x' ↑! U ^ lA)
  dec-var-var {x = x} {x' = x'} Γ≡Δ ⊢x PE.refl ⊢y m≡m with x ≟ x'
  ... | yes PE.refl =  yes (_ , (_ , var-refl ⊢x PE.refl))
  ... | no ¬p = no λ (_ , (_ , eq)) → ¬p (strongVarEq eq)


  dec-castΠ-castΠ : ∀ {Γ Δ A A' X rX Y X' Y' t t' u u' B B' Z rZ W Z' W' e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! [conv↑] Π X' ^ rX ° ⁰ ▹ Y' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Γ ⊢ A' ~ A ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) A) ^ [ % , ι ⁰ ]
              → Δ ⊢ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! [conv↑] Π Z' ^ rZ ° ⁰ ▹ W' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Δ ⊢ B' ~ B ↓! U ⁰ ^ next ⁰
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) B) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → Dec (∃ λ U → ∃ λ lA → Δ ⊢ B ~ A ↓! U ^ lA)
              → ((Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) A e t ~ cast ⁰ (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) B e' u ↑! U ^ lA)
  dec-castΠ-castΠ {rX = rX} {rZ = rZ} Γ≡Δ Π A t eΠA Π' B u eΠB decΠΠ decAB dectu with dec-relevance rX rZ | decΠΠ | decAB
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬AB = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬AB (_ , _ , stability~↓! Γ≡Δ x₁) }
  ... | yes PE.refl | yes ΠΠ′ | yes (_ , _ , AB) with dectu ΠΠ′
  ... | yes p = yes (_ , _ , cast-Π ΠΠ′ (~atU-' A (_ , _ , stability~↓! (symConEq Γ≡Δ) AB)) p eΠA (stabilityTerm (symConEq Γ≡Δ) eΠB))
  ... | no ¬p = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p x₂ }


  dec-castΠΠ%!-castΠΠ%! : ∀ {Γ Δ X Y A B t t' u u' Z W C D e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ ! ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → Dec (Δ ⊢ Π C ^ ! ° ⁰ ▹ D ° ⁰ ° ⁰  ^ ! [conv↑] Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ ι ¹)
              → ((Γ ⊢ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !) e t ~ cast ⁰ (Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ ! ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !) e' u ↑! U ^ lA)
  dec-castΠΠ%!-castΠΠ%! Γ≡Δ t eAB u eCD decΠΠ decΠΠ' dectu with decΠΠ | decΠΠ' 
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬BD (stabilityConv↑Term Γ≡Δ x₁) }
  ... | yes AC | yes BD with dectu AC
  ... | yes p = yes (_ , _ , cast-ΠΠ%! AC (stabilityConv↑Term (symConEq Γ≡Δ) BD) p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec-castΠΠ!%-castΠΠ!% : ∀ {Γ Δ X Y A B t t' u u' Z W C D e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) (Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ % ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → Dec (Δ ⊢ Π C ^ % ° ⁰ ▹ D ° ⁰ ° ⁰  ^ ! [conv↑] Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ ι ¹)
              → ((Γ ⊢ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !) e t ~ cast ⁰ (Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ % ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !) e' u ↑! U ^ lA)
  dec-castΠΠ!%-castΠΠ!% Γ≡Δ t eAB u eCD decΠΠ decΠΠ' dectu with decΠΠ | decΠΠ' 
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬BD (stabilityConv↑Term Γ≡Δ x₁) }
  ... | yes AC | yes BD with dectu AC
  ... | yes p = yes (_ , _ , cast-ΠΠ!% AC (stabilityConv↑Term (symConEq Γ≡Δ) BD) p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬p x₂ }


  dec-castneΠ-castneΠ : ∀ {Γ Δ A A' X Y r t t' e B B' Z W r' v v' e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A (Π X ^ r ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ B ~ B' ↓! U ⁰ ^ next ⁰
              → Δ ⊢ v [conv↑] v' ∷ B ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) B ( Π Z ^ r' ° ⁰ ▹ W ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA)
              → Dec (Γ ⊢ Π Z ^ r' ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! [conv↑] Π X ^ r ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → ((∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA) → Dec (Γ ⊢ t [conv↑] v ∷ A ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A (Π X ^ r ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ B ( Π Z ^ r' ° ⁰ ▹ W ° ⁰ ° ⁰ ^ !) e' v ↑! U ^ lA)
  dec-castneΠ-castneΠ {r = r} {r' = r'} Γ≡Δ A t eℕA B u eℕB decAB decΠΠ dectu with dec-relevance r r' | decΠΠ | decAB
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬AB = no λ { (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → ¬AB (_ , _ , x₁) }
  ... | yes PE.refl | yes ΠΠ′ | yes (_ , _ , AB) with dectu (_ , _ , AB)
  ... | yes tu = yes (_ , _ , cast-neΠ ΠΠ′ (~atU' A (_ , _ , AB)) tu eℕA (stabilityTerm (symConEq Γ≡Δ) eℕB))
  ... | no ¬tu = no λ { (_ , _ , cast-neΠ _ x x₁ x₂ x₃) → ¬tu x₁ }

  dec-castneInd-castneInd : ∀ {Γ Δ i j A A' t t' e B B' v v' e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A (Ind i)) ^ [ % , ι ⁰ ]
              → Δ ⊢ B ~ B' ↓! U ⁰ ^ next ⁰
              → Δ ⊢ v [conv↑] v' ∷ B ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) B (Ind j)) ^ [ % , ι ⁰ ]
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA)
              → ((∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA) → Dec (Γ ⊢ t [conv↑] v ∷ A ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A (Ind i) e t ~ cast ⁰ B (Ind j) e' v ↑! U ^ lA)
  dec-castneInd-castneInd {i = i} {j = j} Γ≡Δ A t eIndA B u eIndB decAB dectu with i ≟ j
  ... | no ¬p = no λ { (_ , _ , cast-neInd x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl with decAB
  ... | no ¬AB = no λ { (_ , _ , cast-neInd x x₁ x₂ x₃) → ¬AB (_ , _ , x) }
  ... | yes AB with dectu AB
  ... | yes tu = yes (_ , _ , cast-neInd (~atU' A AB) tu eIndA (stabilityTerm (symConEq Γ≡Δ) eIndB))
  ... | no ¬tu = no λ { (_ , _ , cast-neInd x x₁ x₂ x₃) → ¬tu x₁ }

  dec-castInd-castInd : ∀ {Γ Δ i j A A' t t' u u' B B' e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A' ~ A ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ Ind i ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Ind i) A) ^ [ % , ι ⁰ ]
              → Δ ⊢ B' ~ B ↓! U ⁰ ^ next ⁰
              → Δ ⊢ u [conv↑] u' ∷ Ind j ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Ind j) B) ^ [ % , ι ⁰ ]
              → Dec (∃ λ U → ∃ λ lA → Δ ⊢ B ~ A ↓! U ^ lA)
              → ((i PE.≡ j) → Dec (Γ ⊢ t [conv↑] u ∷ Ind i ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Ind i) A e t ~ cast ⁰ (Ind j) B e' u ↑! U ^ lA)
  dec-castInd-castInd {i = i} {j = j} Γ≡Δ A t eIndA B u eIndB decAB dectu with i ≟ j
  ... | no ¬p = no λ { (_ , _ , cast-Ind x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl with decAB | dectu PE.refl
  ... | yes (_ , _ , AB) | yes tu = yes (_ , _ , cast-Ind (~atU-' A (_ , _ , stability~↓! (symConEq Γ≡Δ) AB)) tu eIndA (stabilityTerm (symConEq Γ≡Δ) eIndB))
  ... | yes AB | no ¬tu = no λ { (_ , _ , cast-Ind x x₁ x₂ x₃) → ¬tu x₁ }
  ... | no ¬AB | _ = no λ { (_ , _ , cast-Ind x x₁ x₂ x₃) → ¬AB (_ , _ , stability~↓! Γ≡Δ x) }

  dec-castIndΠ-castIndΠ : ∀ {Γ Δ i j X rX Y t t' u u' Z rZ W e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ t [conv↑] t' ∷ Ind i ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Ind i) (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ u [conv↑] u' ∷ Ind j ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Ind j) (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Dec (Δ ⊢ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! [conv↑] Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → ((i PE.≡ j) → Dec (Γ ⊢ t [conv↑] u ∷ Ind i ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Ind i) (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ (Ind j) (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) e' u ↑! U ^ lA)
  dec-castIndΠ-castIndΠ {i = i} {j = j} {rX = rX} {rZ = rZ} Γ≡Δ t eIndΠ u eIndΠ′ decΠΠ dectu with i ≟ j | dec-relevance rX rZ | decΠΠ
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-IndΠ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬p | _ = no λ { (_ , _ , cast-IndΠ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | yes PE.refl | no ¬ΠΠ′ = no λ { (_ , _ , cast-IndΠ x x₁ x₂ x₃) → ¬ΠΠ′ (stabilityConv↑Term Γ≡Δ x) }
  ... | yes PE.refl | yes PE.refl | yes ΠΠ′ with dectu PE.refl
  ... | yes p = yes (_ , _ , cast-IndΠ (stabilityConv↑Term (symConEq Γ≡Δ) ΠΠ′) p eIndΠ (stabilityTerm (symConEq Γ≡Δ) eIndΠ′))
  ... | no ¬p = no λ { (_ , _ , cast-IndΠ x x₁ x₂ x₃) → ¬p x₁ }

  dec-castΠInd-castΠInd : ∀ {Γ Δ i j X rX Y t t' u u' Z rZ W e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) (Ind i)) ^ [ % , ι ⁰ ]
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Ind j)) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → ((Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Ind i) e t ~ cast ⁰ (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Ind j) e' u ↑! U ^ lA)
  dec-castΠInd-castΠInd {i = i} {j = j} {rX = rX} {rZ = rZ} Γ≡Δ t eΠInd u eΠInd′ decΠΠ dectu with i ≟ j | dec-relevance rX rZ | decΠΠ
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-ΠInd x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬p | _ = no λ { (_ , _ , cast-ΠInd x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | yes PE.refl | no ¬ΠΠ′ = no λ { (_ , _ , cast-ΠInd x x₁ x₂ x₃) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes PE.refl | yes ΠΠ′ with dectu ΠΠ′
  ... | yes p = yes (_ , _ , cast-ΠInd ΠΠ′ p eΠInd (stabilityTerm (symConEq Γ≡Δ) eΠInd′))
  ... | no ¬p = no λ { (_ , _ , cast-ΠInd x x₁ x₂ x₃) → ¬p x₁ }


  dec-castIndInd-castIndInd : ∀ {Γ Δ i j k l t t' u u' e e'}
              → ⊢ Γ ≡ Δ
              → reprInd i PE.≢ reprInd k
              → Γ ⊢ t [conv↑] t' ∷ Ind i ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Ind i) (Ind k)) ^ [ % , ι ⁰ ]
              → Δ ⊢ u [conv↑] u' ∷ Ind j ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Ind j) (Ind l)) ^ [ % , ι ⁰ ]
              → ((i PE.≡ j) → Dec (Γ ⊢ t [conv↑] u ∷ Ind i ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Ind i) (Ind k) e t ~ cast ⁰ (Ind j) (Ind l) e' u ↑! U ^ lA)
  dec-castIndInd-castIndInd {i = i} {j = j} {k = k} {l = l} Γ≡Δ i≢k t eIndInd u eIndInd′ dectu with i ≟ j | k ≟ l
  ... | no ¬p | _ = no λ { (_ , _ , cast-IndInd x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬p = no λ { (_ , _ , cast-IndInd x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | yes PE.refl with dectu PE.refl
  ... | yes p = yes (_ , _ , cast-IndInd i≢k p eIndInd (stabilityTerm (symConEq Γ≡Δ) eIndInd′))
  ... | no ¬p = no λ { (_ , _ , cast-IndInd x x₁ x₂ x₃) → ¬p x₁ }

abstract


  dec-emptyrec-emptyrec : ∀ {Γ Δ k l F G lF k' l' F' G' lF'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ F [conv↑] G ^ [ ! , ι lF ]
              → Γ ⊢ k ~ l ↑% sEmpty ^ ι ⁰
              → Δ ⊢ F' [conv↑] G' ^ [ ! , ι lF' ]
              → Δ ⊢ k' ~ l' ↑% sEmpty ^ ι ⁰
              → ((lF PE.≡ lF') → Dec (Γ ⊢ F [conv↑] F' ^ [ ! , ι lF ]))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ Emptyrec lF ⁰ F k ~ Emptyrec lF' ⁰ F' k' ↑! U ^ lA)
  dec-emptyrec-emptyrec {lF = lF} {lF' = lF'} Γ≡Δ F k G k₀ decF with dec-level lF lF' 
  ... | no ¬p = no (λ { (_ , .(ι lF) , Emptyrec-cong x x₁) → ¬p PE.refl })
  ... | yes PE.refl with decF PE.refl
  ... | yes p = let ⊢k , _  = soundness~↑% k
                    ⊢k₀ , _ = soundness~↑% k₀
                    ⊢Γ = wfTerm ⊢k
                in yes (_ , _ , Emptyrec-cong p (%~↑ ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₀)))
  ... | no ¬p = no (λ { (_ , .(ι lF) , Emptyrec-cong x x₁) → ¬p x })


-- IndRect uses a map-spine, so we invert IndRect-cong through propositional
-- equations instead of matching on dual IndRect-cong derivations.
IndRect-inv-head : ∀ {Γ i i' lG lG' P Q t u ms ns k k' A lA}
                 → Γ ⊢ k ~ k' ↑! A ^ lA
                 → k PE.≡ IndRect i lG P t ms
                 → k' PE.≡ IndRect i' lG' Q u ns
                 → i PE.≡ i' × lG PE.≡ lG'
IndRect-inv-head (IndRect-cong _ _ _ _) eq eq' with IndRect-PE-injectivity eq | IndRect-PE-injectivity eq'
... | PE.refl , PE.refl , _ | PE.refl , PE.refl , _ = PE.refl , PE.refl
IndRect-inv-head (var-refl _ _) () _
IndRect-inv-head (app-cong _ _) () _
IndRect-inv-head (Emptyrec-cong _ _) () _
IndRect-inv-head (cast-cong _ _ _ _ _) () _
IndRect-inv-head (cast-refl _ _ _) () _
IndRect-inv-head (cast-refl' _ _ _) _ ()
IndRect-inv-head (cast-neΠ _ _ _ _ _) () _
IndRect-inv-head (cast-Π _ _ _ _ _) () _
IndRect-inv-head (cast-ΠΠ%! _ _ _ _ _) () _
IndRect-inv-head (cast-ΠΠ!% _ _ _ _ _) () _
IndRect-inv-head (cast-neInd _ _ _ _) () _
IndRect-inv-head (cast-Ind _ _ _ _) () _
IndRect-inv-head (cast-IndΠ _ _ _ _) () _
IndRect-inv-head (cast-ΠInd _ _ _ _) () _
IndRect-inv-head (cast-IndInd _ _ _ _) () _

IndRect-inv : ∀ {Γ ind lG P Q t u ms ns k k' A lA}
            → ind ∈ₗ senv
            → Γ ⊢ k ~ k' ↑! A ^ lA
            → k PE.≡ IndRect (SI.SInd.name ind) lG P t ms
            → k' PE.≡ IndRect (SI.SInd.name ind) lG Q u ns
            → (Γ ∙ Ind (SI.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P [conv↑] Q ^ [ ! , ι lG ])
              × (Γ ⊢ t ~ u ↓! Ind (SI.SInd.name ind) ^ ι ⁰)
              × All₃ (λ m m' B → Γ ⊢ m [conv↑] m' ∷ B ^ ι lG) ms ns (indRectBranchTyList ind P ! lG)
IndRect-inv ind∈ (IndRect-cong ind∈′ x x₁ x₂) eq eq' with IndRect-PE-injectivity eq | IndRect-PE-injectivity eq'
... | name≡ , PE.refl , PE.refl , PE.refl , PE.refl | _ , _ , PE.refl , PE.refl , PE.refl with SI.name-inj senv (proj₁ swf) ind∈′ ind∈ name≡
... | PE.refl = x , x₁ , x₂
IndRect-inv _ (var-refl _ _) () _
IndRect-inv _ (app-cong _ _) () _
IndRect-inv _ (Emptyrec-cong _ _) () _
IndRect-inv _ (cast-cong _ _ _ _ _) () _
IndRect-inv _ (cast-refl _ _ _) () _
IndRect-inv _ (cast-refl' _ _ _) _ ()
IndRect-inv _ (cast-neΠ _ _ _ _ _) () _
IndRect-inv _ (cast-Π _ _ _ _ _) () _
IndRect-inv _ (cast-ΠΠ%! _ _ _ _ _) () _
IndRect-inv _ (cast-ΠΠ!% _ _ _ _ _) () _
IndRect-inv _ (cast-neInd _ _ _ _) () _
IndRect-inv _ (cast-Ind _ _ _ _) () _
IndRect-inv _ (cast-IndΠ _ _ _ _) () _
IndRect-inv _ (cast-ΠInd _ _ _ _) () _
IndRect-inv _ (cast-IndInd _ _ _ _) () _

abstract
  dec-IndRect-IndRect : ∀ {Γ ind ind' lG lG' P Q t t' u ms ns}
              → ind ∈ₗ senv
              → ind' ∈ₗ senv
              → Γ ⊢ t ~ t' ↓! Ind (SI.SInd.name ind) ^ ι ⁰
              → ((ind PE.≡ ind') → (lG PE.≡ lG') → Dec (Γ ∙ Ind (SI.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P [conv↑] Q ^ [ ! , ι lG ]))
              → ((ind PE.≡ ind') → (lG PE.≡ lG') → Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↓! U ^ lA))
              → ((ind PE.≡ ind') → (lG PE.≡ lG') → (Γ ∙ Ind (SI.SInd.name ind) ^ [ ! , ι ⁰ ] ⊢ P [conv↑] Q ^ [ ! , ι lG ]) →
                     Dec (All₃ (λ m m' B → Γ ⊢ m [conv↑] m' ∷ B ^ ι lG) ms ns (indRectBranchTyList ind P ! lG)))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ IndRect (SI.SInd.name ind) lG P t ms ~ IndRect (SI.SInd.name ind') lG' Q u ns ↑! U ^ lA)
  dec-IndRect-IndRect {ind = ind} {ind' = ind'} {lG = lG} {lG' = lG'} ind∈ ind∈' t~ decP dect decms
    with SI.SInd.name ind ≟ SI.SInd.name ind' | dec-level lG lG'
  ... | no ¬p | _ = no (λ (_ , _ , X) → ¬p (proj₁ (IndRect-inv-head X PE.refl PE.refl)))
  ... | yes _ | no ¬p = no (λ (_ , _ , X) → ¬p (proj₂ (IndRect-inv-head X PE.refl PE.refl)))
  ... | yes name≡ | yes PE.refl with SI.name-inj senv (proj₁ swf) ind∈ ind∈' name≡
  ... | PE.refl with decP PE.refl PE.refl
  ... | no ¬P = no (λ (_ , _ , X) → ¬P (proj₁ (IndRect-inv ind∈ X PE.refl PE.refl)))
  ... | yes P~ with dect PE.refl PE.refl | decms PE.refl PE.refl P~
  ... | yes tu | yes ms~ = yes (_ , _ , let _ , ⊢t , _ = syntacticEqTerm (soundness~↓! t~) in IndRect-cong ind∈ P~ (~atInd ⊢t tu) ms~)
  ... | yes _ | no ¬ms = no (λ (_ , _ , X) → ¬ms (proj₂ (proj₂ (IndRect-inv ind∈ X PE.refl PE.refl))))
  ... | no ¬tu | _ = no (λ (_ , _ , X) → ¬tu (_ , _ , proj₁ (proj₂ (IndRect-inv ind∈ X PE.refl PE.refl))))

-- Inversion of algorithmic equality of constructors (cf. IndRect-inv).
-- The type index is generalized, since dual ctr-cong matching does not unify.
ctr-inv : ∀ {Γ ind j j' as bs Ts t u i'}
        → ind ∈ₗ senv
        → SI.ctrArgsTypeList ind j PE.≡ just Ts
        → Γ ⊢ t [conv↓] u ∷ Ind i' ^ ι ⁰
        → t PE.≡ ctr (SI.SInd.name ind) j as
        → u PE.≡ ctr (SI.SInd.name ind) j' bs
        → j PE.≡ j' × All₃ (λ a a' A → Γ ⊢ a [conv↑] a' ∷ A ^ ι ⁰) as bs (map emb-stype Ts)
ctr-inv ind∈ argsTy (ctr-cong _ ind∈′ argsTy′ ps) eq eq' with ctr-PE-injectivity eq | ctr-PE-injectivity eq'
... | name≡ , PE.refl , PE.refl | _ , PE.refl , PE.refl with SI.name-inj senv (proj₁ swf) ind∈′ ind∈ name≡
... | PE.refl with PE.trans (PE.sym argsTy) argsTy′
... | PE.refl = PE.refl , ps
ctr-inv _ _ (Ind-ins x) eq _ = ⊥-elim (ctr≢ne (proj₁ (proj₂ (ne~↓! x))) (PE.sym eq))
ctr-inv _ _ (ne-ins _ _ () _) _ _

reflAll₂ : ∀ {Γ as as' As l}
         → All₃ (λ a a' A → Γ ⊢ a [conv↑] a' ∷ A ^ l) as as' As
         → All₂ (λ A B → Γ ⊢ A ≡ B ^ [ ! , l ]) As As
reflAll₂ []ₐ = []ₐ
reflAll₂ (p ∷ₐ ps) = refl (proj₁ (syntacticEqTerm (soundnessConv↑Term p))) ∷ₐ reflAll₂ ps

ctr-ne-inv : ∀ {Γ i j as t u i'}
           → Γ ⊢ t [conv↓] u ∷ Ind i' ^ ι ⁰
           → t PE.≡ ctr i j as
           → Neutral u
           → ⊥
ctr-ne-inv (ctr-cong _ _ _ _) _ neU = ctr≢ne neU PE.refl
ctr-ne-inv (Ind-ins x) eq _ = ctr≢ne (proj₁ (proj₂ (ne~↓! x))) (PE.sym eq)
ctr-ne-inv (ne-ins _ _ () _) _ _
