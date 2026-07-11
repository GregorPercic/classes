{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product

open import Syntax
open import Substitutions
open import Proof
open import Theory


-- The Conservation Theorem 

_↔_ : Set → Set → Set
ty ↔ ty' = (ty → ty') × (ty' → ty)

conservation-⇒ : ∀ {C Γ} φ → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
conservation-⇒ = {!!}

conservation-⇐ : ∀ {C Γ} φ → Proof ST {𝟘} {Γ} (inj-formula φ) → Proof CT {C} {Γ} (inj-formula φ)
conservation-⇐ = {!!}

conservation : ∀ {C Γ} φ → Proof CT {C} {Γ} (inj-formula φ) ↔ Proof ST {𝟘} {Γ} (inj-formula φ)
conservation φ = conservation-⇒ φ , conservation-⇐ φ