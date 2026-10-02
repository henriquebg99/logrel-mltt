-- Embedding of the typing judgements of OTerms (Definition.OTyped) into the
-- typing judgements of Terms.

{-# OPTIONS --safe #-}

import Definition.SUntyped as SI
import Definition.Equiv as E
module Definition.Typed.Embedding (senv : SI.SEnv) (equivs : E.Equivs senv) where

open import Definition.Untyped senv equivs
open import Definition.Typed senv equivs
open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.List using (List; map; _∈ₗ_)
import Tools.List as TL
import Tools.PropositionalEquality as PE
import Definition.SUntyped as SU
import Definition.OUntyped senv as OU
import Definition.OTyped senv as OT

emb-∈ : ∀ {x A r Γ} (h : OT._∷_^_∈_ x A r Γ) →
  x ∷ emb-oterm A ^ r ∈ emb-con Γ
emb-∈ (OT.here {Γ = Γ} {A = A} {r = r}) =
  PE.subst (λ t → _∷_^_∈_ 0 t r (_∙_^_ (emb-con Γ) (emb-oterm A) r))
    (PE.sym (emb-wk1 A)) here
emb-∈ (OT.there {Γ = Γ} {A = A} {rA = rA} {B = B} {rB = rB} {x = x} h) =
  PE.subst (λ t → _∷_^_∈_ (Nat.suc x) t rA (_∙_^_ (emb-con Γ) (emb-oterm B) rB))
    (PE.sym (emb-wk1 A)) (there (emb-∈ h))

mutual
  emb-⊢∷-sgType : ∀ {Γ t G r s} (⊢t : OT._⊢_∷_^_ Γ t (G OU.[ s ]) r) →
    emb-con Γ ⊢ emb-oterm t ∷ emb-oterm G [ emb-oterm s ] ^ r
  emb-⊢∷-sgType {Γ} {t} {G} {r} {s} ⊢t =
    PE.subst (λ B → _⊢_∷_^_ (emb-con Γ) (emb-oterm t) B r)
      (emb-sgSubst G s) (emb-⊢∷ ⊢t)


  emb-⊢All : ∀ {Γ args As r} → OT._⊢All_∷_^_ Γ args As r
    → emb-con Γ ⊢All emb-oterm-all args ∷ map emb-oterm As ^ r
  emb-⊢All OT.εⱼ = εⱼ
  emb-⊢All (OT.consⱼ ⊢t ⊢ts) = consⱼ (emb-⊢∷ ⊢t) (emb-⊢All ⊢ts)

  emb-⊢ : ∀ {Γ} → OT.⊢ Γ → ⊢ emb-con Γ
  emb-⊢ OT.ε = ε
  emb-⊢ (OT._∙_ ⊢Γ ⊢A) = emb-⊢ ⊢Γ ∙ emb-⊢ty ⊢A

  emb-⊢ty : ∀ {Γ A r} → OT._⊢_^_ Γ A r → emb-con Γ ⊢ (emb-oterm A) ^ r
  emb-⊢ty (OT.Uⱼ ⊢Γ) = Uⱼ (emb-⊢ ⊢Γ)
  emb-⊢ty (OT.univ A) = univ (emb-⊢∷ A)

  emb-⊢∷ : ∀ {Γ t A r} → OT._⊢_∷_^_ Γ t A r
         → emb-con Γ ⊢ emb-oterm t ∷ (emb-oterm A) ^ r
  emb-⊢∷ (OT.univ <l ⊢Γ) = univ <l (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.Emptyⱼ ⊢Γ) = Emptyⱼ (emb-⊢ ⊢Γ)
  emb-⊢∷ (OT.Πⱼ abs₁ ▹ abs₂ ▹ dom ▹ cod) =
    Πⱼ abs₁ ▹ abs₂ ▹ (emb-⊢∷ dom) ▹ (emb-⊢∷ cod)
  emb-⊢∷ (OT.var ⊢Γ x∈Γ) = var (emb-⊢ ⊢Γ) (emb-∈ x∈Γ)
  emb-⊢∷ (OT.lamⱼ abs₁ abs₂ dom t) =
    lamⱼ abs₁ abs₂ (emb-⊢ty dom) (emb-⊢∷ t)
  emb-⊢∷ {Γ = Γ} (OT._▹_▹_▹_∘ⱼ_ {g = g} {a = a} {F = F} {G = Gₜ} {lG = lG} {r = r} {lΠ = lΠ} abs ⊢F ⊢Gderiv ⊢gderiv ⊢aderiv) =
    PE.subst (λ (A : Term) → emb-con Γ ⊢ emb-oterm (g OU.∘ a ^ lΠ) ∷ A ^ [ r , ι lG ])
         (PE.sym (emb-sgSubst Gₜ a))
         (PE.subst (λ (t : Term) → emb-con Γ ⊢ t ∷ emb-oterm Gₜ [ emb-oterm a ] ^ [ r , ι lG ])
           (emb-∘ g a lΠ)
           (_▹_▹_▹_∘ⱼ_ {G = emb-oterm Gₜ} abs (emb-⊢∷ ⊢F) (emb-⊢∷ ⊢Gderiv) (emb-⊢∷ ⊢gderiv) (emb-⊢∷ ⊢aderiv)))
  emb-⊢∷ (OT.fstⱼ A B A' B' e) =
    fstⱼ (emb-⊢∷ A) (emb-⊢∷ B) (emb-⊢∷ A') (emb-⊢∷ B') (emb-⊢∷ e)
  emb-⊢∷ {Γ = Γ} (OT.sndⱼ {A = Aₒ} {A' = A'ₒ} {rA = rA} {B = Bₒ} {B' = B'ₒ} {e = e} ⊢A ⊢B ⊢A' ⊢B' ⊢e) =
    PE.subst (λ (A : Term) → _⊢_∷_^_ (emb-con Γ) (emb-oterm (OU.snd e)) A ([ % , ι ⁰ ]))
      (emb-snd-Π-type {Aₒ} {A'ₒ} {rA} {Bₒ} {B'ₒ} e)
      (PE.subst (λ (t : Term) → _⊢_∷_^_ (emb-con Γ) t
                   (Π (emb-oterm A'ₒ) ^ rA ° ⁰ ▹ Id (U ⁰)
                     (emb-oterm Bₒ [ cast ⁰ (wk1 (emb-oterm A'ₒ)) (wk1 (emb-oterm Aₒ))
                       (Idsym (Univ rA ⁰) (wk1 (emb-oterm Aₒ)) (wk1 (emb-oterm A'ₒ))
                         (fst (wk1 (emb-oterm e)))) (var 0) ]↑)
                     (emb-oterm B'ₒ) ° ⁰ ° ⁰ ^ %)
                   ([ % , ι ⁰ ]))
        (PE.sym (emb-snd e))
        (sndⱼ (emb-⊢∷ ⊢A) (emb-⊢∷ ⊢B) (emb-⊢∷ ⊢A') (emb-⊢∷ ⊢B') (emb-⊢∷ ⊢e)))
  emb-⊢∷ (OT.Indⱼ ⊢Γ ind∈) = Indⱼ (emb-⊢ ⊢Γ) ind∈
  emb-⊢∷ {Γ = Γ} (OT.Ctrⱼ {ind} {j} {args} {Ts} ⊢Γ ind∈ eq args∈) =
    PE.subst (λ t → _⊢_∷_^_ (emb-con Γ) t (Ind (SU.SInd.name ind)) ([ ! , ι ⁰ ]))
      (PE.sym (emb-ctr (SU.SInd.name ind) j args))
      (Ctrⱼ (emb-⊢ ⊢Γ) ind∈ eq (PE.subst (λ As → emb-con Γ ⊢All map emb-oterm args ∷ As ^ [ ! , ι ⁰ ])
                     (PE.trans (map-map emb-oterm OU.emb-stype-oterm (Ts))
                       (map-cong (Ts) emb-stype-hom))
                     (PE.subst (λ ts → emb-con Γ ⊢All ts ∷ map emb-oterm (map OU.emb-stype-oterm (Ts)) ^ [ ! , ι ⁰ ])
                              (emb-oterm-all-map args)
                              (emb-⊢All args∈))))
  emb-⊢∷ {Γ = Γ} (OT.IndRectⱼ {ind} {P} {rG} {lG} {t} {ms} abs ind∈ ⊢P ⊢t ⊢ms) =
    PE.subst (λ Ty → _⊢_∷_^_ (emb-con Γ) (emb-oterm (OU.IndRect (SU.SInd.name ind) lG P t ms)) Ty ([ rG , ι lG ]))
      (PE.sym (emb-sgSubst P t))
      (PE.subst (λ tm → _⊢_∷_^_ (emb-con Γ) tm (emb-oterm P [ emb-oterm t ]) ([ rG , ι lG ]))
        (PE.sym (emb-IndRect (SU.SInd.name ind) lG P t ms))
        (IndRectⱼ abs ind∈ (emb-⊢ty ⊢P) (emb-⊢∷ ⊢t)
          (PE.subst (λ As → emb-con Γ ⊢All emb-oterm-all ms ∷ As ^ [ rG , ι lG ])
                    (emb-indRectBranchTyList ind P rG lG)
                    (emb-⊢All ⊢ms))))
  emb-⊢∷ (OT.Emptyrecⱼ A e) = Emptyrecⱼ (emb-⊢ty A) (emb-⊢∷ e)
  emb-⊢∷ (OT.Idⱼ A t u) = Idⱼ (emb-⊢∷ A) (emb-⊢∷ t) (emb-⊢∷ u)
  emb-⊢∷ (OT.Idreflⱼ t) = Idreflⱼ (emb-⊢∷ t)
  emb-⊢∷ {Γ = Γ} (OT.transpⱼ {A = A} {P = P} {t = t} {s = s} {u = u} {e = e} ⊢A ⊢P ⊢t ⊢s ⊢u ⊢e) =
    PE.subst (λ Ty → _⊢_∷_^_ (emb-con Γ) (emb-oterm (OU.transp A P t s u e)) Ty ([ % , ι ⁰ ]))
      (PE.sym (emb-sgSubst P u))
      (PE.subst (λ tm → _⊢_∷_^_ (emb-con Γ) tm (emb-oterm P [ emb-oterm u ]) ([ % , ι ⁰ ]))
        (PE.sym (emb-transp A P t s u e))
        (transpⱼ (emb-⊢ty ⊢A) (emb-⊢ty ⊢P) (emb-⊢∷ ⊢t) (emb-⊢∷-sgType {G = P} {s = t} ⊢s) (emb-⊢∷ ⊢u) (emb-⊢∷ ⊢e)))
  emb-⊢∷ (OT.castⱼ A B e t) =
    castⱼ (emb-⊢∷ A) (emb-⊢∷ B) (emb-⊢∷ e) (emb-⊢∷ t)
  emb-⊢∷ (OT.conv t pAB) = conv (emb-⊢∷ t) (emb-⊢≡ pAB)

  emb-⊢≡ : ∀ {Γ A B r} → OT._⊢_≡_^_ Γ A B r → emb-con Γ ⊢ emb-oterm A ≡ emb-oterm B ^ r
  emb-⊢≡ (OT.refl A) = refl (emb-⊢ty A)
  emb-⊢≡ (OT.sym pAB) = sym (emb-⊢≡ pAB)
  emb-⊢≡ (OT.trans pAB pBC) = trans (emb-⊢≡ pAB) (emb-⊢≡ pBC)
  emb-⊢≡ (OT.univ pAB) = univ (emb-⊢≡∷ pAB)

  emb-⊢≡∷-sgType : ∀ {Γ t u G s r} (⊢tu : OT._⊢_≡_∷_^_ Γ t u (G OU.[ s ]) r) →
    emb-con Γ ⊢ emb-oterm t ≡ emb-oterm u ∷ emb-oterm G [ emb-oterm s ] ^ r
  emb-⊢≡∷-sgType {Γ} {t} {u} {G} {s} {r} ⊢tu =
    PE.subst (λ B → _⊢_≡_∷_^_ (emb-con Γ) (emb-oterm t) (emb-oterm u) B r)
      (emb-sgSubst G s) (emb-⊢≡∷ ⊢tu)





  emb-⊢≡∷-ηPremise : ∀ {Γ' f g G l lG} (pf0g0 : OT._⊢_≡_∷_^_ Γ' (OU.wk1 f OU.∘ OU.var Nat.zero ^ l) (OU.wk1 g OU.∘ OU.var Nat.zero ^ l) G ([ ! , ι lG ])) →
    emb-con Γ' ⊢ wk1 (emb-oterm f) ∘ var Nat.zero ^ l
      ≡ wk1 (emb-oterm g) ∘ var Nat.zero ^ l ∷ emb-oterm G ^ [ ! , ι lG ]
  emb-⊢≡∷-ηPremise {Γ' = Γ'} {f = f} {g = g} {G = G} {l = l} {lG = lG} pf0g0 =
    let x' = wk1 (emb-oterm f) ∘ var Nat.zero ^ l
    in PE.subst (λ u → emb-con Γ' ⊢ x' ≡ u ∷ emb-oterm G ^ [ ! , ι lG ])
         (emb-wk1∘var g l)
         (PE.subst (λ t → emb-con Γ' ⊢ t ≡ emb-oterm (OU.wk1 g OU.∘ OU.var Nat.zero ^ l) ∷ emb-oterm G ^ [ ! , ι lG ])
           (emb-wk1∘var f l)
           (emb-⊢≡∷ pf0g0))

  emb-⊢≡∷ : ∀ {Γ t u A r} → OT._⊢_≡_∷_^_ Γ t u A r
           → emb-con Γ ⊢ emb-oterm t ≡ emb-oterm u ∷ (emb-oterm A) ^ r
  emb-⊢≡∷ (OT.refl t) = refl (emb-⊢∷ t)
  emb-⊢≡∷ (OT.sym ptu) = sym (emb-⊢≡∷ ptu)
  emb-⊢≡∷ (OT.trans ptu puv) = trans (emb-⊢≡∷ ptu) (emb-⊢≡∷ puv)
  emb-⊢≡∷ (OT.conv ptu pAB) = conv (emb-⊢≡∷ ptu) (emb-⊢≡ pAB)
  emb-⊢≡∷ (OT.Π-cong abs₁ abs₂ dom⊢ pDomH pCodE) =
    Π-cong abs₁ abs₂ (emb-⊢ty dom⊢) (emb-⊢≡∷ pDomH) (emb-⊢≡∷ pCodE)
  emb-⊢≡∷ {Γ = Γ} (OT.app-cong {a = a} {G = G} {lG = lG} pfg pab) =
    let pf = app-cong (emb-⊢≡∷ pfg) (emb-⊢≡∷ pab)
    in PE.subst (λ (B : Term) → emb-con Γ ⊢ _ ≡ _ ∷ B ^ [ ! , ι lG ])
         (PE.sym (emb-sgSubst G a))
         pf
  emb-⊢≡∷ {Γ = Γ} (OT.β-red {a = a} {t = t} {G = G} {lG = lG} lF≤l lG≤l dom⊢ t₁ a₁) =
    let pf = β-red lF≤l lG≤l (emb-⊢ty dom⊢) (emb-⊢∷ t₁) (emb-⊢∷ a₁)
        lhs = (lam _ ▹ emb-oterm t ^ _) ∘ emb-oterm a ^ _
    in PE.subst (λ (B : Term) → emb-con Γ ⊢ lhs ≡ emb-oterm (t OU.[ a ]) ∷ B ^ [ ! , ι lG ])
         (PE.sym (emb-sgSubst G a))
         (PE.subst (λ (u : Term) → emb-con Γ ⊢ lhs ≡ u ∷ emb-oterm G [ emb-oterm a ] ^ [ ! , ι lG ])
           (PE.sym (emb-sgSubst t a))
           pf)
  emb-⊢≡∷ (OT.η-eq lF≤l lG≤l dom⊢ f g pf0g0) =
    η-eq lF≤l lG≤l (emb-⊢ty dom⊢) (emb-⊢∷ f) (emb-⊢∷ g) (emb-⊢≡∷-ηPremise pf0g0)
  emb-⊢≡∷ (OT.Emptyrec-cong pAA' e e') =
    Emptyrec-cong (emb-⊢≡ pAA') (emb-⊢∷ e) (emb-⊢∷ e')
  emb-⊢≡∷ (OT.proof-irrelevance t u) =
    proof-irrelevance (emb-⊢∷ t) (emb-⊢∷ u)
  emb-⊢≡∷ (OT.Id-cong pAA' ptt' puu') =
    Id-cong (emb-⊢≡∷ pAA') (emb-⊢≡∷ ptt') (emb-⊢≡∷ puu')
  emb-⊢≡∷ (OT.cast-refl pAB e t) =
    cast-refl (emb-⊢≡∷ pAB) (emb-⊢∷ e) (emb-⊢∷ t)
  emb-⊢≡∷ (OT.cast-cong pAA' pBB' ptt' e e') =
    cast-cong (emb-⊢≡∷ pAA') (emb-⊢≡∷ pBB') (emb-⊢≡∷ ptt') (emb-⊢∷ e) (emb-⊢∷ e')
  emb-⊢≡∷ {Γ = Γ} (OT.cast-Π {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} {f = f} ⊢A ⊢B ⊢A' ⊢B' ⊢e ⊢f) =
    let l   = ⁰
        LHS = emb-oterm (OU.cast l (OU.Π A ^ rA ° l ▹ B ° l ° l ^ !) (OU.Π A' ^ rA ° l ▹ B' ° l ° l ^ !) e f)
        pf  = cast-Π (emb-⊢∷ ⊢A) (emb-⊢∷ ⊢B) (emb-⊢∷ ⊢A') (emb-⊢∷ ⊢B') (emb-⊢∷ ⊢e) (emb-⊢∷ ⊢f)
    in PE.subst (λ rhs → emb-con Γ ⊢ LHS ≡ rhs ∷ (emb-oterm (OU.Π A' ^ rA ° l ▹ B' ° l ° l ^ !)) ^ [ ! , ι l ])
         (PE.sym (emb-castΠ-lamBody {A} {A'} {rA} {B} {B'} {e} {f}))
         pf
  emb-⊢≡∷ (OT.cast-Ind-refl ind∈ ⊢e ⊢t) = cast-Ind-refl ind∈ (emb-⊢∷ ⊢e) (emb-⊢∷ ⊢t)
