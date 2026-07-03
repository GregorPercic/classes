{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product

open import Syntax
open import Substitutions
open import Theory
open import Proof


-- The theory of classes

data idxCT : Set where
  -- the axiom schema y ∈ { x | Φ } ⇔ Φ[y/x]
  set∈class : ∀ n Γ (y : Var Γ) (Φ : Formula (Fin n) (extend Γ)) → idxCT
  -- the axiom A ∈ B ⇔ ∃x.(x = A ∧ x ∈ B)
  class∈class : idxCT
  -- the axiom A = B ⇔ ∀x.(x ∈ A ⇔ x ∈ B)
  class≈class : idxCT

data twoClasses : Set where
  A B : twoClasses

CT : Theory
thy-idx CT = idxCT

thy-cls CT (set∈class n Γ y Φ) = Fin n
thy-cls CT class∈class = twoClasses
thy-cls CT class≈class = twoClasses

thy-ctx CT (set∈class n Γ y Φ) = Γ
thy-ctx CT class∈class = ⟨⟩
thy-ctx CT class≈class = ⟨⟩

thy-axi CT (set∈class n Γ y Φ) = svar y ∈ class Φ ⇔ Φ [ svar y ]
thy-axi CT class∈class = cvar A ∈ cvar B ⇔ exists (svar zero ≈ cvar A ∧ svar zero ∈ cvar B) -- perhaps a bad formulation
thy-axi CT class≈class = cvar A ≈ cvar B ⇔ all (svar zero ∈ cvar A ⇔ svar zero ∈ cvar B)

-- The basic first-order set theory with Extensionality as its only axiom

data idxST : Set where
  ext : idxST

ST : Theory
thy-idx ST = idxST

thy-cls ST ext = 𝟘

thy-ctx ST ext = ⟨⟩

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
elim (svar x ∈ class Φ) = (elim Φ) ⟦ svar x ⟧
elim (class Φ ∈ svar x) = some ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-bind-zero (elim Φ))) ∧ svar zero ∈ svar (suc x))
elim (class Φ ∈ class Ψ) = some ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-bind-zero (elim Φ))) ∧ elim Ψ)
elim (Φ ∧ Ψ) = elim Φ ∧ elim Ψ
elim (Φ ⇔ Ψ) = elim Φ ⇔ elim Ψ
elim (¬ Φ) = ¬ (elim Φ)
elim (all Φ) = all (elim Φ)

main-theorem : ∀ {Γ} (Φ : Formula₀ Γ) → Proof CT (Φ ⇔ (inj-formula (elim Φ)))
main-theorem Φ = {!!}

eliminability : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → Proof CT (Subst-Formula σ Φ ⇔ inj-formula (elim (Subst-Formula σ Φ)))
eliminability C Φ σ  = main-theorem (Subst-Formula σ Φ)

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