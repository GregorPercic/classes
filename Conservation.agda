{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product

open import Syntax
open import Substitutions
open import Proof
open import Theory


-- The Conservation Theorem 

_↔_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
ty ↔ ty' = (ty → ty') × (ty' → ty)

transport-proof : ∀ {T C Γ} {Φ Ψ : Formula C Γ} → (Φ ≡ Ψ) → Proof T Φ → Proof T Ψ
transport-proof {T = T} e p = ≡-subst (λ Ξ → Proof T Ξ) e p

conservation-⇒ : ∀ {C Γ} {Φ : Formula C Γ} (φ : formula Γ) → (Φ ≡ inj-formula φ) → Proof CT {C} {Γ} Φ → Proof ST {𝟘} {Γ} (inj-formula φ)
conservation-⇒ φ e (axiom (set∈class D Γ y Φ) σ r) = {!  !}
conservation-⇒ φ e (axiom class∈class σ r) = {!   !}
conservation-⇒ φ e (axiom class≈class σ r) = {!   !}
conservation-⇒ φ e ⇔-refl = {!   !}
conservation-⇒ φ e (∧-cong p p') = {!   !}
conservation-⇒ φ e (⇔-cong p p') = {!   !}
conservation-⇒ φ e (¬-cong p) = {!   !}
conservation-⇒ φ e (all-cong p) = {!   !}
conservation-⇒ φ e (⇔-trans p p') = {!   !}
conservation-⇒ φ e (exists-cong p) = {!   !}

conservation-⇐-lemma : ∀ {Γ} {Φ : Formula₀ Γ} → Proof ST {𝟘} {Γ} Φ → Proof CT {𝟘} {Γ} Φ
conservation-⇐-lemma (axiom ext σ r) =
  Subst-Proof σ (ren-Proof r (axiom class≈class (λ {A → svar (suc zero) ; B → svar zero}) empty-ren))
conservation-⇐-lemma ⇔-refl = ⇔-refl
conservation-⇐-lemma (∧-cong p p') = ∧-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (⇔-cong p p') = ⇔-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (¬-cong p) = ¬-cong (conservation-⇐-lemma p)
conservation-⇐-lemma (all-cong p) = all-cong (conservation-⇐-lemma p)
conservation-⇐-lemma (⇔-trans p p') = ⇔-trans (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (exists-cong p) = exists-cong (conservation-⇐-lemma p)

conservation-⇐ : ∀ {C Γ} (φ : formula Γ) → Proof ST {𝟘} {Γ} (inj-formula φ) → Proof CT {C} {Γ} (inj-formula φ)
conservation-⇐ φ p =
  ≡-subst
    (λ Ξ → Proof CT Ξ)
    Subst-empty-id
    (Subst-Proof empty-Subst (conservation-⇐-lemma {Φ = inj-formula φ} p))

conservation : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) ↔ Proof ST {𝟘} {Γ} (inj-formula φ)
conservation φ = conservation-⇒ φ refl , conservation-⇐ φ