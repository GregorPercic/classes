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

actP : ∀ {T C Γ Δ} {Φ : Formula C Γ} (ρ : subst Γ Δ) → Proof T Φ → Proof T (subst-Formula ρ Φ)
actP ρ p = {!!}

ActP : ∀ {T C D Γ} {Φ : Formula C Γ} (σ : Subst Γ C D) → Proof T Φ → Proof T (Subst-Formula σ Φ)
ActP σ p = {!!}

elim : ∀ {Γ} → Formula₀ Γ → formula Γ
elim (svar x ≈ svar y) = svar x ≈ svar y
elim (svar x ≈ class Φ) = all (svar zero ∈ svar (suc x) ⇔ elim Φ)
elim (class Φ ≈ svar x) = all (elim Φ ⇔ svar zero ∈ svar (suc x))
elim (class Φ ≈ class Ψ) = all (elim Φ ⇔ elim Ψ)
elim (svar x ∈ svar y) = svar x ∈ svar y
elim (svar x ∈ class Φ) = (elim Φ) [ svar x ]f
elim (class Φ ∈ svar x) = some ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-ctx (elim Φ))) ∧ svar zero ∈ svar (suc x))
elim (class Φ ∈ class Ψ) = some ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-ctx (elim Φ))) ∧ elim Ψ)
elim (Φ ∧ Ψ) = elim Φ ∧ elim Ψ
elim (Φ ⇔ Ψ) = elim Φ ⇔ elim Ψ
elim (¬ Φ) = ¬ (elim Φ)
elim (all Φ) = all (elim Φ)

subst-dist-⇔ : ∀ {Γ T} {Φ Ψ : Formula₀ (extend Γ)} (x : Var Γ) → Proof T (Φ ⇔ Ψ) → Proof T (Φ [ svar x ]F ⇔ Ψ [ svar x ]F)
subst-dist-⇔ x p = all-elim (all-intro p)

eq-to-⇔ : ∀ {Γ C T} {Φ Ψ : Formula Γ C} → Φ ≡ Ψ → Proof T (Φ ⇔ Ψ)
eq-to-⇔ refl = ⇔-refl

subst-inj-commute : ∀ {Γ} {φ : formula (extend Γ)} {x : Var Γ} → _[_]F {C = 𝟘} (inj-formula φ) (svar x) ≡ inj-formula (φ [ svar x ]f)
subst-inj-commute {φ = φ} =
  trans
    ren-is-subst-var-Formula
    (trans
      subst-inj-commute-ren
      (cong inj-formula (sym ren-is-subst-var-formula)))

axiom-unsubst : 
  ∀ {T} (i : thy-idx T) →
  -----------------------
  Proof T (thy-axi T i)
axiom-unsubst i = {!  !}

⇔-∈-subst : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → Proof CT (svar zero ∈ (class (extend-Formula-ctx Φ)) ⇔ (extend-Formula-ctx Φ) [ svar zero ]F)
⇔-∈-subst {Γ} {Φ} = axiom-unsubst (set∈class 0 (extend Γ) zero (extend-Formula-ctx Φ))

eq-subst-zero-Formula : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → (extend-Formula-ctx Φ) [ svar zero ]F ≡ Φ
eq-subst-zero-Formula {Φ = Φ} = trans
    (≡-subst
      (λ f → (extend-Formula-ctx Φ [ svar zero ]F) ≡ ren-Formula f Φ)
      contract-extend-ren-suc-id
      (trans
        (subst-zero-is-contract-Formula {Φ = (extend-Formula-ctx Φ)})
        (ren-comp-Formula (extend-ren suc) contract)))
    id-ren-Formula

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
    lemma1 = axiom class≈class Subst-AB (λ y → svar x) -- NASTY HACK!!!

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
eliminability-main-theorem (class Φ ≈ svar x) = {!  !}
eliminability-main-theorem (class Φ ≈ class Ψ) = {!   !}
eliminability-main-theorem (svar x ∈ svar y) = ⇔-refl
eliminability-main-theorem {Γ = Γ} (svar x ∈ class Φ) =
  ⇔-trans
    lemma
    (eq-to-⇔ (subst-inj-commute {φ = elim Φ}))
  where
    lemma : Proof CT (svar x ∈ class Φ ⇔ (inj-formula (elim Φ)) [ svar x ]F)
    lemma =
      ⇔-trans
        (axiom-unsubst (set∈class 0 Γ x Φ))
        (subst-dist-⇔ x (eliminability-main-theorem Φ))
eliminability-main-theorem (class Φ ∈ svar x) = {!   !}
eliminability-main-theorem (class Φ ∈ class Ψ) = {!   !}
eliminability-main-theorem (Φ ∧ Ψ) = ∧-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ⇔ Ψ) = ⇔-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (¬ Φ) = ¬-cong (eliminability-main-theorem Φ)
eliminability-main-theorem (all Φ) = all-cong (eliminability-main-theorem Φ)

eliminability : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → Proof CT (Subst-Formula σ Φ ⇔ inj-formula (elim (Subst-Formula σ Φ)))
eliminability C Φ σ  = eliminability-main-theorem (Subst-Formula σ Φ)

corollary : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → ∃[ φ ] Proof CT (Subst-Formula σ Φ ⇔ inj-formula φ)
corollary C Φ σ = elim (Subst-Formula σ Φ) , eliminability C Φ σ


-- eliminability-The conservation theorem 

_↔_ : Set → Set → Set
ty ↔ ty' = (ty → ty') × (ty' → ty)

conservation-⇒ : ∀ {C Γ} φ → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
conservation-⇒ = {!!}

conservation-⇐ : ∀ {C Γ} φ → Proof ST {𝟘} {Γ} (inj-formula φ) → Proof CT {C} {Γ} (inj-formula φ)
conservation-⇐ = {!!}

conservation : ∀ {C Γ} φ → Proof CT {C} {Γ} (inj-formula φ) ↔ Proof ST {𝟘} {Γ} (inj-formula φ)
conservation φ = conservation-⇒ φ , conservation-⇐ φ