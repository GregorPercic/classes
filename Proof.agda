open import Syntax
open import Substitutions

open import Theory

-- The notion of proof: maybe notation "p : T ⊢ ϕ" means p is a proof of Φ in T
data Proof (T : Theory) {C : Set} : {Γ : Ctx} → Formula C Γ → Set where
  axiom :
    ∀ {Γ} (i : thy-idx T)
    (σ : Subst Γ (thy-cls T i) C)
    (ρ : subst (thy-ctx T i) Γ) →
    Proof T (Subst-Formula σ (subst-Formula ρ (thy-axi T i)))

  refl : ∀ {Γ} {t : Term C Γ} → Proof T (t ≈ t)

  ∧-intro :
    ∀ {Γ} {Φ Ψ : Formula C Γ} →
    Proof T Φ →
    Proof T Ψ →
    ---------------
    Proof T (Φ ∧ Ψ)

  all-elim :
    ∀ {Γ} {Φ : Formula C (extend Γ)} {t : term Γ} →
    Proof T (all Φ) →
    ---------------------------
    Proof T (Φ [ t ])