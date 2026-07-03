open import Syntax public

-- We define renamings first.

ren : Ctx → Ctx → Set
ren Γ Δ = Var Γ → Var Δ

extend-ren : ∀ {Γ Δ} → ren Γ Δ → ren (extend Γ) (extend Δ)
extend-ren ρ zero = zero
extend-ren ρ (suc x) = suc (ρ x)

ren-term : ∀ {Γ Δ} → ren Γ Δ → term Γ → term Δ
ren-term ρ (svar x) = svar (ρ x)

ren-formula : ∀ {Γ Δ} → ren Γ Δ → formula Γ → formula Δ
ren-formula r (t ≈ u) = ren-term r t ≈ ren-term r u
ren-formula r (t ∈ u) = ren-term r t ∈ ren-term r u
ren-formula r (φ ∧ ψ) = ren-formula r φ ∧ ren-formula r ψ
ren-formula r (φ ⇔ ψ) = ren-formula r φ ⇔ ren-formula r ψ
ren-formula r (¬ φ) = ¬ (ren-formula r φ)
ren-formula r (all φ) = all (ren-formula (extend-ren r) φ)

mutual
  ren-Term : ∀ {C Γ Δ} → ren Γ Δ → Term C Γ → Term C Δ
  ren-Term r (svar x) = svar (r x)
  ren-Term r (cvar A) = cvar A
  ren-Term r (class Φ) = class (ren-Formula (extend-ren r) Φ)

  ren-Formula : ∀ {C Γ Δ} → ren Γ Δ → Formula C Γ → Formula C Δ
  ren-Formula r (t ≈ u) = ren-Term r t ≈ ren-Term r u
  ren-Formula r (t ∈ u) = ren-Term r t ∈ ren-Term r u
  ren-Formula r (Φ ∧ Ψ) = ren-Formula r Φ ∧ ren-Formula r Ψ
  ren-Formula r (Φ ⇔ Ψ) = ren-Formula r Φ ⇔ ren-Formula r Ψ
  ren-Formula r (¬ Φ) = ¬ (ren-Formula r Φ)
  ren-Formula r (all Φ) = all (ren-Formula (extend-ren r) Φ)

ren-bind-zero : ∀ {Γ} → ren Γ (extend Γ)
ren-bind-zero zero = zero
ren-bind-zero (suc x) = suc (suc x)


-- Renamings give us substitutions.

Subst : Ctx → Set → Set → Set
Subst Γ C D  = C → Term D Γ

subst : Ctx → Ctx → Set
subst Γ Δ = Var Γ → term Δ

extend-term : ∀ {Γ} → term Γ → term (extend Γ)
extend-term = ren-term suc

extend-subst : ∀ {Γ Δ} → subst Γ Δ → subst (extend Γ) (extend Δ)
extend-subst ρ zero = svar zero
extend-subst ρ (suc x) = extend-term (ρ x)

subst-formula : ∀ {Γ Δ} → subst Γ Δ → formula Γ → formula Δ
subst-formula ρ (svar x ≈ svar y) = ρ x ≈ ρ y
subst-formula ρ (svar x ∈ svar y) = ρ x ∈ ρ y
subst-formula ρ (φ ∧ ψ) = subst-formula ρ φ ∧ subst-formula ρ ψ
subst-formula ρ (φ ⇔ ψ) = subst-formula ρ φ ⇔ subst-formula ρ ψ
subst-formula ρ (¬ φ) = ¬ (subst-formula ρ φ)
subst-formula ρ (all φ) = all (subst-formula (extend-subst ρ) φ)

mutual
  subst-Term : ∀ {C : Set} {Γ Δ} → subst Γ Δ → Term C Γ → Term C Δ
  subst-Term ρ (svar x) = inj-term (ρ x)
  subst-Term ρ (cvar c) = cvar c
  subst-Term ρ (class Φ) = class (subst-Formula (extend-subst ρ) Φ) -- need to skip bound variable x in { x | Φ }

  subst-Formula : ∀ {C : Set} {Γ Δ} → subst Γ Δ → Formula C Γ → Formula C Δ
  subst-Formula ρ (t ≈ u) = (subst-Term ρ t) ≈ (subst-Term ρ u)
  subst-Formula ρ (t ∈ u) = (subst-Term ρ t) ∈ (subst-Term ρ u)
  subst-Formula ρ (Φ ∧ Ψ) = (subst-Formula ρ Φ) ∧ (subst-Formula ρ Ψ)
  subst-Formula ρ (Φ ⇔ Ψ) = (subst-Formula ρ Φ) ⇔ (subst-Formula ρ Ψ)
  subst-Formula ρ (¬ Φ) = ¬ (subst-Formula ρ Φ)
  subst-Formula ρ (all Φ) = all (subst-Formula (extend-subst ρ) Φ) -- need to skip bound variable x in ∀x.Φ

compRS : ∀ {Γ Δ C D} → ren Γ Δ → Subst Γ C D → Subst Δ C D
compRS r σ x = ren-Term r (σ x)

extend-Subst : ∀ {Γ C D} → Subst Γ C D → Subst (extend Γ) C D
extend-Subst σ = compRS suc σ

mutual
  Subst-Term : ∀ {C D : Set} {Γ} → Subst Γ C D → Term C Γ → Term D Γ
  Subst-Term σ (svar x) = svar x
  Subst-Term σ (cvar c) = σ c
  Subst-Term σ (class Φ) = class (Subst-Formula (extend-Subst σ) Φ)

  Subst-Formula : ∀ {C D : Set} {Γ} → Subst  Γ C D → Formula C Γ → Formula D Γ
  Subst-Formula σ (t ≈ u) = (Subst-Term σ t) ≈ (Subst-Term σ u)
  Subst-Formula σ (t ∈ u) = (Subst-Term σ t) ∈ (Subst-Term σ u)
  Subst-Formula σ (Φ ∧ Ψ) = (Subst-Formula σ Φ) ∧ (Subst-Formula σ Ψ)
  Subst-Formula σ (Φ ⇔ Ψ) = (Subst-Formula σ Φ) ⇔ (Subst-Formula σ Ψ)
  Subst-Formula σ (¬ Φ) = ¬ (Subst-Formula σ Φ)
  Subst-Formula {Γ = Γ} σ (all Φ) = all (Subst-Formula (extend-Subst σ) Φ)

-- Simple substitution of one term

subst₀ : ∀ {Γ : Ctx} → term Γ → subst (extend Γ) Γ
subst₀ t zero = t
subst₀ t (suc x) = svar x

_[_] : ∀ {Γ C} → Formula C (extend Γ) → term Γ → Formula C Γ
Φ [ t ] = subst-Formula (subst₀ t) Φ

_⟦_⟧ : ∀ {Γ} → formula (extend Γ) → term Γ → formula Γ
φ ⟦ t ⟧ = subst-formula (subst₀ t) φ


-- Infrastructure for extending other constructs

extend-formula : ∀ {Γ} → formula Γ → formula (extend Γ)
extend-formula = ren-formula suc

extend-formula-bind-zero : ∀ {Γ} → formula Γ → formula (extend Γ)
extend-formula-bind-zero = ren-formula ren-bind-zero

extend-Term : ∀ {Γ C} → Term C Γ → Term C (extend Γ)
extend-Term = ren-Term suc


record Sbs (C : Set) (Γ : Ctx) (D : Set) (Δ : Ctx) : Set where
  field
    sbs-cls : C → Term D Δ
    sbs-set : Var Γ → term Δ