open import Data.Product

open import Syntax
open import Substitutions
open import Proof
open import Theory
open import Eliminability


_↔_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
ty ↔ ty' = (ty → ty') × (ty' → ty)

transport-proof : ∀ {T C Γ} {Φ Ψ : Formula C Γ} → (Φ ≡ Ψ) → Proof T Φ → Proof T Ψ
transport-proof {T = T} e p = ≡-subst (λ Ξ → Proof T Ξ) e p

r-inj-∧ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ∧ Ψ ≡ Φ' ∧ Ψ') → Ψ ≡ Ψ'
r-inj-∧ refl = refl

l-inj-∧ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ∧ Ψ ≡ Φ' ∧ Ψ') → Φ ≡ Φ'
l-inj-∧ refl = refl

r-inj-⇔ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ⇔ Ψ) ≡ (Φ' ⇔ Ψ') → Ψ ≡ Ψ'
r-inj-⇔ refl = refl

l-inj-⇔ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ⇔ Ψ) ≡ (Φ' ⇔ Ψ') → Φ ≡ Φ'
l-inj-⇔ refl = refl

inj-¬ : ∀ {C Γ} {Φ Φ' : Formula C Γ} → ¬ Φ ≡ ¬ Φ' → Φ ≡ Φ'
inj-¬ refl = refl

inj-all : ∀ {C Γ} {Φ Φ' : Formula C (extend Γ)} → all Φ ≡ all Φ' → Φ ≡ Φ'
inj-all refl = refl

inj-exists : ∀ {C Γ} {Φ Φ' : Formula C (extend Γ)} → exists Φ ≡ exists Φ' → Φ ≡ Φ'
inj-exists refl = refl

l-inj-≈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ≈ t') ≡ (u ≈ u') → t ≡ u
l-inj-≈ refl = refl

r-inj-≈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ≈ t') ≡ (u ≈ u') → t' ≡ u'
r-inj-≈ refl = refl

l-inj-∈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ∈ t') ≡ (u ∈ u') → t ≡ u
l-inj-∈ refl = refl

r-inj-∈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ∈ t') ≡ (u ∈ u') → t' ≡ u'
r-inj-∈ refl = refl


inj-formula-injective : ∀ {C Γ} {φ ψ : formula Γ} → inj-formula {C = C} φ ≡ inj-formula ψ → φ ≡ ψ
inj-formula-injective {φ = svar x ≈ svar y} {ψ = svar x' ≈ svar y'} refl = refl
inj-formula-injective {φ = svar x ∈ svar y} {ψ = svar x' ∈ svar y'} refl = refl
inj-formula-injective {φ = φ ∧ φ'} {ψ = ψ ∧ ψ'} e = cong₂ _∧_ (inj-formula-injective (l-inj-∧ e)) (inj-formula-injective (r-inj-∧ e))
inj-formula-injective {φ = φ ⇔ φ'} {ψ = ψ ⇔ ψ'} e = cong₂ _⇔_ (inj-formula-injective (l-inj-⇔ e)) (inj-formula-injective (r-inj-⇔ e))
inj-formula-injective {φ = ¬ φ} {ψ = ¬ ψ} e = cong ¬_ (inj-formula-injective (inj-¬ e))
inj-formula-injective {φ = all φ} {ψ = all ψ} e = cong all (inj-formula-injective (inj-all e))
inj-formula-injective {φ = exists φ} {ψ = exists ψ} e = cong exists (inj-formula-injective (inj-exists e))

conservation-⇐-lemma : ∀ {Γ} {Φ : Formula₀ Γ} → Proof ST {𝟘} {Γ} Φ → Proof CT {𝟘} {Γ} Φ
conservation-⇐-lemma (axiom (ext Γ x y) σ r) =
  Subst-Proof σ (ren-Proof r (axiom class≈class (λ {A → svar x ; B → svar y}) empty-ren))
conservation-⇐-lemma ⇔-refl = ⇔-refl
conservation-⇐-lemma (∧-cong p p') = ∧-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (⇔-cong p p') = ⇔-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (¬-cong p) = ¬-cong (conservation-⇐-lemma p)
conservation-⇐-lemma (all-cong p) = all-cong (conservation-⇐-lemma p)
conservation-⇐-lemma (⇔-trans p p') = ⇔-trans (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (exists-cong p) = exists-cong (conservation-⇐-lemma p)

conservation-⇐ : ∀ {C Γ} (φ : formula Γ) → Proof ST {𝟘} {Γ} (inj-formula φ) → Proof CT {C} {Γ} (inj-formula φ)
conservation-⇐ φ p =
  transport-proof
    Subst-empty-id
    (Subst-Proof empty-Subst (conservation-⇐-lemma {Φ = inj-formula φ} p))

svar-injective : ∀ {C Γ} {x y : Var Γ} → Term.svar {C = C} x ≡ svar y → x ≡ y
svar-injective refl = refl

magic-Subst : ∀ {C D Γ} → Subst Γ C D
magic-Subst _ = class (svar zero ≈ svar zero)

inj-formula-Subst-id : ∀ {C D Γ} {φ : formula Γ} (σ : Subst Γ C D) → Subst-Formula σ (inj-formula φ) ≡ inj-formula {C = D} φ
inj-formula-Subst-id {φ = svar x ≈ svar y} σ = refl
inj-formula-Subst-id {φ = svar x ∈ svar y} σ = refl
inj-formula-Subst-id {φ = φ ∧ ψ} σ = cong₂ _∧_ (inj-formula-Subst-id σ) (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = φ ⇔ ψ} σ = cong₂ _⇔_ (inj-formula-Subst-id σ) (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = ¬ φ} σ = cong ¬_ (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = all φ} σ = cong all (inj-formula-Subst-id (extend-Subst σ))
inj-formula-Subst-id {φ = exists φ} σ = cong exists (inj-formula-Subst-id (extend-Subst σ))

mutual
  Lemma : ∀ {C Γ} {φ : formula Γ} {Φ : Formula C Γ} → (Φ ≡ inj-formula φ) → Proof CT {C} {Γ} Φ → Proof ST {𝟘} {Γ} (inj-formula φ)
  Lemma {φ = svar x ∈ svar x' ⇔ ψ} () (axiom (set∈class C Γ y Φ) σ r)
  Lemma {φ = svar x ∈ svar y ⇔ exists (svar zero ≈ svar x' ∧ svar zero ∈ svar y')} e (axiom class∈class σ r) =
    ≡-subst₂
      (λ t u → Proof ST (svar x ∈ svar y ⇔ exists (svar zero ≈ t ∧ svar zero ∈ u)))
      lemma3
      lemma4
      {!   !}
    where
      lemma1 : σ A ≡ svar x
      lemma1 = l-inj-∈ (l-inj-⇔ e)

      lemma2 : σ B ≡ svar y
      lemma2 = r-inj-∈ (l-inj-⇔ e)

      lemma3-1 : extend-Subst σ A ≡ svar x'
      lemma3-1 = r-inj-≈ (l-inj-∧ (inj-exists (r-inj-⇔ e)))

      lemma3-2 : extend-Subst σ A ≡ svar (suc x)
      lemma3-2 = cong (λ t → ren-Term suc t) lemma1

      -- we also do conversion from C to 𝟘 by descending to variable names
      lemma3 : svar (suc x) ≡ svar x'
      lemma3 = cong svar (svar-injective (trans (sym lemma3-2) lemma3-1))

      lemma4-1 : extend-Subst σ B ≡ svar y'
      lemma4-1 = r-inj-∈ (r-inj-∧ (inj-exists (r-inj-⇔ e)))

      lemma4-2 : extend-Subst σ B ≡ svar (suc y)
      lemma4-2 = cong (λ t → ren-Term suc t) lemma2

      lemma4 : svar (suc y) ≡ svar y'
      lemma4 = cong svar (svar-injective (trans (sym lemma4-2) lemma4-1))
  Lemma {φ = svar x ≈ svar y ⇔ all (svar zero ∈ svar x' ⇔ svar zero ∈ svar y')} e (axiom class≈class σ r) = {!   !}
  Lemma {φ = φ ⇔ φ'} e ⇔-refl =
    eq-to-⇔
      (cong
        inj-formula
        (inj-formula-injective
          (trans (sym (l-inj-⇔ e)) (r-inj-⇔ e))))
  Lemma {φ = φ ∧ φ' ⇔ ψ ∧ ψ'} refl (∧-cong p p') = ∧-cong (Lemma refl p) (Lemma refl p')
  Lemma {φ = (φ ⇔ φ') ⇔ (ψ ⇔ ψ')} refl (⇔-cong p p') = ⇔-cong (Lemma refl p) (Lemma refl p')
  Lemma {φ = ¬ φ ⇔ ¬ ψ} refl (¬-cong p) = ¬-cong (Lemma refl p)
  Lemma {φ = all φ ⇔ all ψ} refl (all-cong p) = all-cong (Lemma refl p)
  Lemma {φ = φ ⇔ ψ} refl (⇔-trans {Φ' = Φ'} p p') with existential-eliminability _ Φ' magic-Subst
  ... | θ , equiv =
    ⇔-trans
      -- termination check fails here
      (Lemma refl (≡-subst (λ Ξ → Proof CT (Ξ ⇔ _)) (inj-formula-Subst-id magic-Subst) (⇔-trans (Subst-Proof magic-Subst p) equiv)))
      {!   !}
  Lemma {φ = exists φ ⇔ exists ψ} refl (exists-cong p) = exists-cong (Lemma refl p)

  Lemma' : ∀ {C Γ} {φ : formula Γ} {Φ : Formula C Γ} → Proof CT (Φ ⇔ inj-formula φ) → Proof CT {C} {Γ} Φ → Proof ST {𝟘} {Γ} (inj-formula φ)
  Lemma' eq p = {!   !}

conservation-⇒ : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
conservation-⇒ φ p = Lemma refl p

conservation-⇒' : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
conservation-⇒' φ p = Lemma' ⇔-refl p

-- The Conservation Theorem

conservation : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) ↔ Proof ST {𝟘} {Γ} (inj-formula φ)
-- conservation φ = conservation-⇒ φ , conservation-⇐ φ
conservation φ = conservation-⇒' φ , conservation-⇐ φ