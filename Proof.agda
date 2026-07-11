open import Syntax
open import Substitutions

open import Theory

-- The notion of proof: maybe notation "p : T ⊢ ϕ" means p is a proof of Φ in T
data Proof (T : Theory) {C : Set} : {Γ : Ctx} → Formula C Γ → Set where
  axiom :
    ∀ {Γ} (i : thy-idx T)
    (σ : Subst Γ (thy-cls T i) C)
    (r : ren (thy-ctx T i) Γ) →
    Proof T (Subst-Formula σ (ren-Formula r (thy-axi T i)))

  all-intro :
    ∀ {Γ} {Φ : Formula C (extend Γ)} →
    Proof T Φ →
    ---------------
    Proof T (all Φ)

  ⇔-refl : ∀ {Γ} {Φ : Formula C Γ} → Proof T (Φ ⇔ Φ)

  ∧-cong : ∀ {Γ} {Φ Φ' Ψ Ψ' : Formula C Γ} →
    Proof T (Φ ⇔ Φ') →
    Proof T (Ψ ⇔ Ψ') →
    -------------------------
    Proof T (Φ ∧ Ψ ⇔ Φ' ∧ Ψ')

  ⇔-cong : ∀ {Γ} {Φ Φ' Ψ Ψ' : Formula C Γ} →
    Proof T (Φ ⇔ Φ') →
    Proof T (Ψ ⇔ Ψ') →
    ------------------------------
    Proof T ((Φ ⇔ Ψ) ⇔ (Φ' ⇔ Ψ'))

  ¬-cong : ∀ {Γ} {Φ Φ' : Formula C Γ} →
    Proof T (Φ ⇔ Φ') →
    --------------------
    Proof T (¬ Φ ⇔ ¬ Φ')

  all-cong : ∀ {Γ} {Φ Φ' : Formula C (extend Γ)} →
    Proof T (Φ ⇔ Φ') →
    -------------------------
    Proof T (all Φ ⇔ all Φ')
  
  ⇔-trans : ∀ {Γ} {Φ Φ' Φ'' : Formula C Γ} →
    Proof T (Φ ⇔ Φ') →
    Proof T (Φ' ⇔ Φ'') →
    ---------------------
    Proof T (Φ ⇔ Φ'')
  
  exists-cong : ∀ {Γ} {Φ Φ' : Formula C (extend Γ)} →
    Proof T (Φ ⇔ Φ') →
    ------------------------------
    Proof T (exists Φ ⇔ exists Φ')