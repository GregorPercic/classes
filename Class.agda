{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product

open import Syntax
open import Substitutions
open import Theory
open import Proof


-- The theory of classes

data idxCT : Set where
  -- the axiom schema y ∈ { x | Φ } ⇔ Φ[y/x]
  set∈class : ∀ n Γ (y : Var Γ) (Φ : Formula (Fin-with-𝟘 n) (extend Γ)) → idxCT
  -- the axiom A ∈ B ⇔ ∃x.(x = A ∧ x ∈ B)
  class∈class : idxCT
  -- the axiom A = B ⇔ ∀x.(x ∈ A ⇔ x ∈ B)
  class≈class : idxCT

data twoClasses : Set where
  A B : twoClasses

CT : Theory
thy-idx CT = idxCT

thy-cls CT (set∈class n Γ y Φ) = Fin-with-𝟘 n
thy-cls CT class∈class = twoClasses
thy-cls CT class≈class = twoClasses

thy-ctx CT (set∈class n Γ y Φ) = Γ
thy-ctx CT class∈class = ⟨⟩
thy-ctx CT class≈class = ⟨⟩

thy-axi CT (set∈class n Γ y Φ) = svar y ∈ class Φ ⇔ Φ [ svar y ]F
thy-axi CT class∈class = cvar A ∈ cvar B ⇔ exists (svar zero ≈ cvar A ∧ svar zero ∈ cvar B) -- perhaps a bad formulation
thy-axi CT class≈class = cvar A ≈ cvar B ⇔ all (svar zero ∈ cvar A ⇔ svar zero ∈ cvar B)

-- The basic first-order set theory with Extensionality as its only axiom

data idxST : Set where
  ext : idxST

ST : Theory
thy-idx ST = idxST

thy-cls ST ext = 𝟘

thy-ctx ST ext = ⟨⟩
-- the axiom of extensionality: ∀x∀y.(x = y ⇔ ∀z.(z ∈ x ⇔ z ∈ y))
thy-axi ST ext = all (all (svar (suc zero) ≈ svar zero ⇔ all (svar zero ∈ svar (suc (suc zero)) ⇔ svar zero ∈ svar (suc zero))))

extend-comp-rS-commute : ∀ {C D Γ Δ} (r : ren Γ Δ) (σ : Subst Γ C D) →
  comp-rS (extend-ren r) (extend-Subst σ) ≡ extend-Subst (comp-rS r σ)
extend-comp-rS-commute {C = C} r σ = fun-ext lemma
  where
    lemma : (x : C) →
      comp-rS (extend-ren r) (extend-Subst σ) x ≡ extend-Subst (comp-rS r σ) x
    lemma x = renaming-suc-commute-Term r

mutual
  comp-rS-Term : ∀ {C D Γ Δ} {t : Term C Γ} (σ : Subst Γ C D) (r : ren Γ Δ) →
    ren-Term r (Subst-Term σ t) ≡ Subst-Term (comp-rS r σ) (ren-Term r t)
  comp-rS-Term {t = svar x} σ r = refl
  comp-rS-Term {t = cvar c} σ r = refl
  comp-rS-Term {t = class Φ} σ r =
    cong
      class
      (trans
        (comp-rS-Formula {Φ = Φ} (extend-Subst σ) (extend-ren r))
        (cong
          (λ σ' → Subst-Formula σ' (ren-Formula (extend-ren r) Φ))
          (extend-comp-rS-commute r σ)))

  comp-rS-Formula : ∀ {C D Γ Δ} {Φ : Formula C Γ} (σ : Subst Γ C D) (r : ren Γ Δ) →
    ren-Formula r (Subst-Formula σ Φ) ≡ Subst-Formula (comp-rS r σ) (ren-Formula r Φ)
  comp-rS-Formula {Φ = t ≈ u} σ r = cong₂ _≈_ (comp-rS-Term {t = t} σ r) (comp-rS-Term {t = u} σ r)
  comp-rS-Formula {Φ = t ∈ u} σ r = cong₂ _∈_ (comp-rS-Term {t = t} σ r) (comp-rS-Term {t = u} σ r)
  comp-rS-Formula {Φ = Φ ∧ Ψ} σ r = cong₂ _∧_ (comp-rS-Formula {Φ = Φ} σ r) (comp-rS-Formula {Φ = Ψ} σ r)
  comp-rS-Formula {Φ = Φ ⇔ Ψ} σ r = cong₂ _⇔_ (comp-rS-Formula {Φ = Φ} σ r) (comp-rS-Formula {Φ = Ψ} σ r)
  comp-rS-Formula {Φ = ¬ Φ} σ r = cong ¬_ (comp-rS-Formula {Φ = Φ} σ r)
  comp-rS-Formula {Φ = all Φ} σ r =
    cong
      all
      (trans
        (comp-rS-Formula {Φ = Φ} (extend-Subst σ) (extend-ren r))
        (cong
          (λ σ' → Subst-Formula σ' (ren-Formula (extend-ren r) Φ))
          (extend-comp-rS-commute r σ)))
  comp-rS-Formula {Φ = exists Φ} σ r =
    cong
      exists
      (trans
        (comp-rS-Formula {Φ = Φ} (extend-Subst σ) (extend-ren r))
        (cong
          (λ σ' → Subst-Formula σ' (ren-Formula (extend-ren r) Φ))
          (extend-comp-rS-commute r σ)))

ren-Proof : ∀ {T C Γ Δ} {Φ : Formula C Γ} (r : ren Γ Δ) → Proof T Φ → Proof T (ren-Formula r Φ)
ren-Proof {T = T} r (axiom i σ r') =
  ≡-subst
    (λ Ξ → Proof T Ξ)
    (sym
      (trans
        (comp-rS-Formula {Φ = ren-Formula r' (thy-axi T i)} σ r)
        (cong (λ Ξ → Subst-Formula (comp-rS r σ) Ξ) (ren-comp-Formula r' r))))
    (axiom i (comp-rS r σ) (r ∘ r'))
ren-Proof r (all-intro p) = all-intro (ren-Proof (extend-ren r) p)
ren-Proof r ⇔-refl = ⇔-refl
ren-Proof r (∧-cong p p') = ∧-cong (ren-Proof r p) (ren-Proof r p')
ren-Proof r (⇔-cong p p') = ⇔-cong (ren-Proof r p) (ren-Proof r p')
ren-Proof r (¬-cong p) = ¬-cong (ren-Proof r p)
ren-Proof r (all-cong p) = all-cong (ren-Proof (extend-ren r) p)
ren-Proof r (⇔-trans p p') = ⇔-trans (ren-Proof r p) (ren-Proof r p')
ren-Proof r (exists-cong p) = exists-cong (ren-Proof (extend-ren r) p)

-- Subst-Proof : ∀ {T C D Γ} {Φ : Formula C Γ} (σ : Subst Γ C D) → Proof T Φ → Proof T (Subst-Formula σ Φ)
-- Subst-Proof σ p = {!!}

elim : ∀ {Γ} → Formula₀ Γ → formula Γ
elim (svar x ≈ svar y) = svar x ≈ svar y
elim (svar x ≈ class Φ) = all (svar zero ∈ svar (suc x) ⇔ elim Φ)
elim (class Φ ≈ svar x) = all (elim Φ ⇔ svar zero ∈ svar (suc x))
elim (class Φ ≈ class Ψ) = all (elim Φ ⇔ elim Ψ)
elim (svar x ∈ svar y) = svar x ∈ svar y
elim (svar x ∈ class Φ) = (elim Φ) [ svar x ]f
elim (class Φ ∈ svar x) = exists ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-ctx (elim Φ))) ∧ svar zero ∈ svar (suc x))
elim (class Φ ∈ class Ψ) = exists ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-ctx (elim Φ))) ∧ elim Ψ)
elim (Φ ∧ Ψ) = elim Φ ∧ elim Ψ
elim (Φ ⇔ Ψ) = elim Φ ⇔ elim Ψ
elim (¬ Φ) = ¬ (elim Φ)
elim (all Φ) = all (elim Φ)
elim (exists Φ) = exists (elim Φ)

subst-dist-⇔ : ∀ {Γ T} {Φ Ψ : Formula₀ (extend Γ)} (x : Var Γ) → Proof T (Φ ⇔ Ψ) → Proof T (Φ [ svar x ]F ⇔ Ψ [ svar x ]F)
subst-dist-⇔ x p = ren-Proof (ren₀ x) p -- all-elim (all-intro p) ; if we can cope with having all-elim

eq-to-⇔ : ∀ {Γ C T} {Φ Ψ : Formula Γ C} → Φ ≡ Ψ → Proof T (Φ ⇔ Ψ)
eq-to-⇔ refl = ⇔-refl

axiom-unsubst : 
  ∀ {T} (i : thy-idx T) →
  -----------------------
  Proof T (thy-axi T i)
axiom-unsubst i = {!  !}

⇔-∈-subst : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → Proof CT (svar zero ∈ (class (extend-Formula-ctx Φ)) ⇔ (extend-Formula-ctx Φ) [ svar zero ]F)
⇔-∈-subst {Γ} {Φ} = axiom-unsubst (set∈class 0 (extend Γ) zero (extend-Formula-ctx Φ))

eq-subst-zero-Formula : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → (extend-Formula-ctx Φ) [ svar zero ]F ≡ Φ
eq-subst-zero-Formula {Φ = Φ} =
  trans
    (trans
      (ren-comp-Formula (extend-ren suc) (ren₀ zero))
      (cong
        (λ f → ren-Formula f Φ)
        ren-zero-extend-ctx-id))
    id-ren-Formula

elim-renamings-commute : ∀ {Γ Δ} {Φ : Formula₀ Γ} (r : ren Γ Δ) →
  elim (ren-Formula r Φ) ≡ ren-formula r (elim Φ)
elim-renamings-commute {Φ = svar x ≈ svar y} r = refl
elim-renamings-commute {Φ = svar x ≈ class Φ} r =
  cong (λ Ξ → all (svar zero ∈ svar (suc (r x)) ⇔ Ξ)) (elim-renamings-commute {Φ = Φ} (extend-ren r))
elim-renamings-commute {Φ = class Φ ≈ svar x} r =
  cong (λ Ξ → all (Ξ ⇔ svar zero ∈ svar (suc (r x)))) (elim-renamings-commute {Φ = Φ} (extend-ren r))
elim-renamings-commute {Φ = class Φ ≈ class Ψ} r =
  cong₂
    (λ Ξ Ξ' → all (Ξ ⇔ Ξ'))
    (elim-renamings-commute {Φ = Φ} (extend-ren r))
    (elim-renamings-commute {Φ = Ψ} (extend-ren r))
elim-renamings-commute {Φ = svar x ∈ svar y} r = refl
elim-renamings-commute {Φ = svar x ∈ class Φ} r =
  trans
    (trans
      (trans
        (cong
          (λ e → ren-formula (ren₀ (r x)) e)
          (elim-renamings-commute {Φ = Φ} (extend-ren r)))
        (ren-comp-formula (extend-ren r) (ren₀ (r x))))
      (cong (λ f → ren-formula f (elim Φ)) (lemma r)))
    (sym (ren-comp-formula (ren₀ x) r))
  where
    lemma : ∀ {Γ Δ} {x : Var Γ} (r : ren Γ Δ) → ren₀ (r x) ∘ (extend-ren r) ≡ r ∘ (ren₀ x)
    lemma r = fun-ext λ {zero → refl ; (suc x) → refl}
elim-renamings-commute {Φ = class Φ ∈ svar x} r =
  cong (λ Ξ → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ svar zero ∈ svar (suc (r x)))) lemma
  where
    lemma : extend-formula-ctx (elim (ren-Formula (extend-ren r) Φ)) ≡ ren-formula (extend-ren (extend-ren r)) (extend-formula-ctx (elim Φ))
    lemma =
      trans
        (trans
          (trans
            (cong (λ e → extend-formula-ctx e) (elim-renamings-commute {Φ = Φ} (extend-ren r)))
            (ren-comp-formula (extend-ren r) (extend-ren suc)))
          (cong (λ f → ren-formula f (elim Φ)) (extend-suc-lemma r)))
        (sym (ren-comp-formula (extend-ren suc) (extend-ren (extend-ren r))))
elim-renamings-commute {Φ = class Φ ∈ class Ψ} r =
  cong₂ (λ Ξ Ξ' → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ Ξ')) lemma (elim-renamings-commute {Φ = Ψ} (extend-ren r))
  where
    lemma : extend-formula-ctx (elim (ren-Formula (extend-ren r) Φ)) ≡ ren-formula (extend-ren (extend-ren r)) (extend-formula-ctx (elim Φ))
    lemma =
      trans
        (trans
          (trans
            (cong (λ e → extend-formula-ctx e) (elim-renamings-commute {Φ = Φ} (extend-ren r)))
            (ren-comp-formula (extend-ren r) (extend-ren suc)))
          (cong (λ f → ren-formula f (elim Φ)) (extend-suc-lemma r)))
        (sym (ren-comp-formula (extend-ren suc) (extend-ren (extend-ren r))))
elim-renamings-commute {Φ = Φ ∧ Ψ} r = cong₂ _∧_ (elim-renamings-commute {Φ = Φ} r) (elim-renamings-commute {Φ = Ψ} r)
elim-renamings-commute {Φ = Φ ⇔ Ψ} r = cong₂ _⇔_ (elim-renamings-commute {Φ = Φ} r) (elim-renamings-commute {Φ = Ψ} r)
elim-renamings-commute {Φ = ¬ Φ} r = cong ¬_ (elim-renamings-commute {Φ = Φ} r)
elim-renamings-commute {Φ = all Φ} r = cong all (elim-renamings-commute {Φ = Φ} (extend-ren r))
elim-renamings-commute {Φ = exists Φ} r = cong exists (elim-renamings-commute {Φ = Φ} (extend-ren r))

elim-extend-commute : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → elim (extend-Formula-ctx Φ) ≡ extend-formula-ctx (elim Φ)
elim-extend-commute {Φ = Φ} = elim-renamings-commute {Φ = Φ} (extend-ren suc)

eliminability-main-theorem : ∀ {Γ} (Φ : Formula₀ Γ) → Proof CT (Φ ⇔ (inj-formula (elim Φ)))
eliminability-main-theorem (svar x ≈ svar y) = ⇔-refl
eliminability-main-theorem {Γ = Γ} (svar x ≈ class Φ) = ⇔-trans lemma1 lemma7
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = svar x
    Subst-AB B = class Φ

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = (extend-Formula-ctx Φ)

    lemma1 : Proof CT (svar x ≈ class Φ ⇔ all (svar zero ∈ svar (suc x) ⇔ svar zero ∈ (class Φ+)))
    lemma1 = axiom class≈class Subst-AB (λ ()) -- hack

    lemma2 : Proof CT ((svar zero ∈ svar (suc x) ⇔ svar zero ∈ (class Φ+)) ⇔ (svar zero ∈ svar (suc x) ⇔ Φ+ [ svar zero ]F))
    lemma2 = ⇔-cong ⇔-refl ⇔-∈-subst

    lemma3 : Proof CT ((svar zero ∈ svar (suc x) ⇔ Φ+ [ svar zero ]F) ⇔ (svar zero ∈ svar (suc x) ⇔ Φ))
    lemma3 = ⇔-cong ⇔-refl (eq-to-⇔ eq-subst-zero-Formula)

    lemma4 : Proof CT ((svar zero ∈ svar (suc x) ⇔ svar zero ∈ (class Φ+)) ⇔ (svar zero ∈ svar (suc x) ⇔ Φ))
    lemma4 = ⇔-trans lemma2 lemma3

    lemma5 : Proof CT ((svar zero ∈ svar (suc x) ⇔ Φ) ⇔ (svar zero ∈ svar (suc x) ⇔ inj-formula (elim Φ)))
    lemma5 = ⇔-cong ⇔-refl (eliminability-main-theorem Φ)

    lemma6 : Proof CT ((svar zero ∈ svar (suc x) ⇔ svar zero ∈ (class Φ+)) ⇔ (svar zero ∈ svar (suc x) ⇔ inj-formula (elim Φ)))
    lemma6 = ⇔-trans lemma4 lemma5

    lemma7 : Proof CT (all (svar zero ∈ svar (suc x) ⇔ svar zero ∈ (class Φ+)) ⇔ all (svar zero ∈ svar (suc x) ⇔ inj-formula (elim Φ)))
    lemma7 = all-cong lemma6
eliminability-main-theorem {Γ = Γ} (class Φ ≈ svar x) = ⇔-trans lemma1 lemma7
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = svar x

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = (extend-Formula-ctx Φ)

    lemma1 : Proof CT (class Φ ≈ svar x ⇔ all (svar zero ∈ (class Φ+) ⇔ svar zero ∈ svar (suc x)))
    lemma1 = axiom class≈class Subst-AB (λ ()) -- hack

    lemma2 : Proof CT ((svar zero ∈ (class Φ+) ⇔ svar zero ∈ svar (suc x)) ⇔ (Φ+ [ svar zero ]F ⇔ svar zero ∈ svar (suc x)))
    lemma2 = ⇔-cong ⇔-∈-subst ⇔-refl

    lemma3 : Proof CT ((Φ+ [ svar zero ]F ⇔ svar zero ∈ svar (suc x)) ⇔ (Φ ⇔ svar zero ∈ svar (suc x)))
    lemma3 = ⇔-cong (eq-to-⇔ eq-subst-zero-Formula) ⇔-refl

    lemma4 : Proof CT ((svar zero ∈ (class Φ+) ⇔ svar zero ∈ svar (suc x)) ⇔ (Φ ⇔ svar zero ∈ svar (suc x)))
    lemma4 = ⇔-trans lemma2 lemma3

    lemma5 : Proof CT ((Φ ⇔ svar zero ∈ svar (suc x)) ⇔ (inj-formula (elim Φ) ⇔ svar zero ∈ svar (suc x)))
    lemma5 = ⇔-cong (eliminability-main-theorem Φ) ⇔-refl

    lemma6 : Proof CT ((svar zero ∈ (class Φ+) ⇔ svar zero ∈ svar (suc x)) ⇔ (inj-formula (elim Φ) ⇔ svar zero ∈ svar (suc x)))
    lemma6 = ⇔-trans lemma4 lemma5

    lemma7 : Proof CT (all (svar zero ∈ (class Φ+) ⇔ svar zero ∈ svar (suc x)) ⇔ all (inj-formula (elim Φ) ⇔ svar zero ∈ svar (suc x)))
    lemma7 = all-cong lemma6
eliminability-main-theorem {Γ = Γ} (class Φ ≈ class Ψ) = ⇔-trans lemma1 lemma7
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = class Ψ

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = (extend-Formula-ctx Φ)

    Ψ+ : Formula₀ (extend (extend Γ))
    Ψ+ = (extend-Formula-ctx Ψ)

    lemma1 : Proof CT (class Φ ≈ class Ψ ⇔ all (svar zero ∈ (class Φ+) ⇔ svar zero ∈ (class Ψ+)))
    lemma1 = axiom class≈class Subst-AB (λ ()) -- hack

    lemma2 : Proof CT ((svar zero ∈ (class Φ+) ⇔ svar zero ∈ (class Ψ+)) ⇔ (Φ+ [ svar zero ]F ⇔ Ψ+ [ svar zero ]F))
    lemma2 = ⇔-cong ⇔-∈-subst ⇔-∈-subst

    lemma3 : Proof CT ((Φ+ [ svar zero ]F ⇔ Ψ+ [ svar zero ]F) ⇔ (Φ ⇔ Ψ))
    lemma3 = ⇔-cong (eq-to-⇔ eq-subst-zero-Formula) (eq-to-⇔ eq-subst-zero-Formula)

    lemma4 : Proof CT ((svar zero ∈ (class Φ+) ⇔ svar zero ∈ (class Ψ+)) ⇔ (Φ ⇔ Ψ))
    lemma4 = ⇔-trans lemma2 lemma3

    lemma5 : Proof CT ((Φ ⇔ Ψ) ⇔ (inj-formula (elim Φ) ⇔ inj-formula (elim Ψ)))
    lemma5 = ⇔-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)

    lemma6 : Proof CT ((svar zero ∈ (class Φ+) ⇔ svar zero ∈ (class Ψ+)) ⇔ (inj-formula (elim Φ) ⇔ inj-formula (elim Ψ)))
    lemma6 = ⇔-trans lemma4 lemma5

    lemma7 : Proof CT (all (svar zero ∈ (class Φ+) ⇔ svar zero ∈ (class Ψ+)) ⇔ all (inj-formula (elim Φ) ⇔ inj-formula (elim Ψ)))
    lemma7 = all-cong lemma6
eliminability-main-theorem (svar x ∈ svar y) = ⇔-refl
eliminability-main-theorem {Γ = Γ} (svar x ∈ class Φ) =
  ⇔-trans
    lemma
    (eq-to-⇔ (subst-inj-commute-ren-zero {φ = elim Φ}))
  where
    lemma : Proof CT (svar x ∈ class Φ ⇔ (inj-formula (elim Φ)) [ svar x ]F)
    lemma =
      ⇔-trans
        (axiom-unsubst (set∈class 0 Γ x Φ))
        (subst-dist-⇔ x (eliminability-main-theorem Φ))
eliminability-main-theorem {Γ = Γ} (class Φ ∈ svar x) = ⇔-trans lemma1 lemma12
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = svar x

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = (extend-Formula-ctx Φ)

    Φ++ : Formula₀ (extend (extend (extend Γ)))
    Φ++ = (extend-Formula-ctx Φ+)

    lemma1 : Proof CT (class Φ ∈ svar x ⇔ exists (svar zero ≈ class Φ+ ∧ svar zero ∈ svar (suc x)))
    lemma1 = axiom class∈class Subst-AB (λ ())

    lemma2 : Proof CT (svar zero ≈ class Φ+ ⇔ all (svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++))
    lemma2 = axiom class≈class (λ {A → svar zero ; B → class Φ+}) (λ ())

    lemma3 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ++ [ svar zero ]F)
    lemma3 = ⇔-∈-subst

    lemma4 : Proof CT (Φ++ [ svar zero ]F ⇔ Φ+)
    lemma4 = eq-to-⇔ eq-subst-zero-Formula

    lemma5 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ+)
    lemma5 = ⇔-trans lemma3 lemma4

    -- (ren-Formula (extend-ren suc) Φ)
    --  ⇔ inj-formula (elim (ren-Formula (extend-ren suc) Φ))
    --  ≡ ren-Formula (extend-ren suc) (inj-formula (elim Φ))
    lemma6 : Proof CT (Φ+ ⇔ inj-formula (elim Φ+))
    lemma6 = ≡-subst (λ Ξ → Proof CT (Φ+ ⇔ Ξ)) lemma6-2 lemma6-1
      where
        lemma6-1 : Proof CT (Φ+ ⇔ extend-Formula-ctx (inj-formula (elim Φ)))
        lemma6-1 = ren-Proof (extend-ren suc) (eliminability-main-theorem Φ)

        lemma6-2 : extend-Formula-ctx {C = 𝟘} (inj-formula (elim Φ)) ≡ inj-formula (elim Φ+)
        lemma6-2 =
          trans
            (subst-inj-commute-ren (extend-ren suc))
            (sym 
              (cong
                inj-formula
                (elim-renamings-commute {Φ = Φ} (extend-ren suc))))

    lemma7 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (elim Φ+))
    lemma7 = ⇔-trans lemma5 lemma6

    lemma8 : Proof CT (inj-formula (elim Φ+) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma8 = eq-to-⇔ (cong inj-formula (elim-extend-commute {Φ = Φ}))

    lemma9 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma9 = ⇔-trans lemma7 lemma8

    lemma10 : Proof CT ((svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++) ⇔ (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma10 = ⇔-cong ⇔-refl lemma9

    lemma11 : Proof CT ((svar zero ≈ class Φ+) ⇔ all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma11 = ⇔-trans lemma2 (all-cong lemma10)

    lemma12 : Proof CT ((exists (svar zero ≈ class Φ+ ∧ svar zero ∈ svar (suc x))) ⇔ (exists (all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))) ∧ svar zero ∈ svar (suc x))))
    lemma12 = exists-cong (∧-cong lemma11 ⇔-refl)
eliminability-main-theorem {Γ = Γ} (class Φ ∈ class Ψ) = ⇔-trans lemma1 lemma12
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = class Ψ

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = (extend-Formula-ctx Φ)

    Φ++ : Formula₀ (extend (extend (extend Γ)))
    Φ++ = (extend-Formula-ctx Φ+)

    Ψ+ : Formula₀ (extend (extend Γ))
    Ψ+ = (extend-Formula-ctx Ψ)

    lemma1 : Proof CT (class Φ ∈ class Ψ ⇔ exists (svar zero ≈ class Φ+ ∧ svar zero ∈ class Ψ+))
    lemma1 = axiom class∈class Subst-AB (λ ())

    lemma2 : Proof CT (svar zero ≈ class Φ+ ⇔ all (svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++))
    lemma2 = axiom class≈class (λ {A → svar zero ; B → class Φ+}) (λ ())

    lemma3 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ++ [ svar zero ]F)
    lemma3 = ⇔-∈-subst

    lemma4 : Proof CT (Φ++ [ svar zero ]F ⇔ Φ+)
    lemma4 = eq-to-⇔ eq-subst-zero-Formula

    lemma5 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ+)
    lemma5 = ⇔-trans lemma3 lemma4

    -- (ren-Formula (extend-ren suc) Φ)
    --  ⇔ inj-formula (elim (ren-Formula (extend-ren suc) Φ))
    --  ≡ ren-Formula (extend-ren suc) (inj-formula (elim Φ))
    lemma6 : Proof CT (Φ+ ⇔ inj-formula (elim Φ+))
    lemma6 = ≡-subst (λ Ξ → Proof CT (Φ+ ⇔ Ξ)) lemma6-2 lemma6-1
      where
        lemma6-1 : Proof CT (Φ+ ⇔ extend-Formula-ctx (inj-formula (elim Φ)))
        lemma6-1 = ren-Proof (extend-ren suc) (eliminability-main-theorem Φ)

        lemma6-2 : extend-Formula-ctx {C = 𝟘} (inj-formula (elim Φ)) ≡ inj-formula (elim Φ+)
        lemma6-2 =
          trans
            (subst-inj-commute-ren (extend-ren suc))
            (sym 
              (cong
                inj-formula
                (elim-renamings-commute {Φ = Φ} (extend-ren suc))))

    lemma7 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (elim Φ+))
    lemma7 = ⇔-trans lemma5 lemma6

    lemma8 : Proof CT (inj-formula (elim Φ+) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma8 = eq-to-⇔ (cong inj-formula (elim-extend-commute {Φ = Φ}))

    lemma9 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma9 = ⇔-trans lemma7 lemma8

    lemma10 : Proof CT ((svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++) ⇔ (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma10 = ⇔-cong ⇔-refl lemma9

    lemma11 : Proof CT ((svar zero ≈ class Φ+) ⇔ all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma11 = ⇔-trans lemma2 (all-cong lemma10)

    lemma12 : Proof CT ((exists (svar zero ≈ class Φ+ ∧ svar zero ∈ class Ψ+)) ⇔ (exists (all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))) ∧ inj-formula (elim Ψ))))
    lemma12 = exists-cong (∧-cong lemma11 lemma12-1)
     where
      lemma12-1 : Proof CT (svar zero ∈ class Ψ+ ⇔ inj-formula (elim Ψ))
      lemma12-1 =
        ⇔-trans
          (⇔-trans
            ⇔-∈-subst
            (eq-to-⇔ eq-subst-zero-Formula))
          (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ∧ Ψ) = ∧-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ⇔ Ψ) = ⇔-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (¬ Φ) = ¬-cong (eliminability-main-theorem Φ)
eliminability-main-theorem (all Φ) = all-cong (eliminability-main-theorem Φ)
eliminability-main-theorem (exists Φ) = exists-cong (eliminability-main-theorem Φ)

eliminability : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → Proof CT (Subst-Formula σ Φ ⇔ inj-formula (elim (Subst-Formula σ Φ)))
eliminability C Φ σ  = eliminability-main-theorem (Subst-Formula σ Φ)

corollary : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → ∃[ φ ] Proof CT (Subst-Formula σ Φ ⇔ inj-formula φ)
corollary C Φ σ = elim (Subst-Formula σ Φ) , eliminability C Φ σ


-- The conservation theorem 

_↔_ : Set → Set → Set
ty ↔ ty' = (ty → ty') × (ty' → ty)

conservation-⇒ : ∀ {C Γ} φ → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
conservation-⇒ = {!!}

conservation-⇐ : ∀ {C Γ} φ → Proof ST {𝟘} {Γ} (inj-formula φ) → Proof CT {C} {Γ} (inj-formula φ)
conservation-⇐ = {!!}

conservation : ∀ {C Γ} φ → Proof CT {C} {Γ} (inj-formula φ) ↔ Proof ST {𝟘} {Γ} (inj-formula φ)
conservation φ = conservation-⇒ φ , conservation-⇐ φ