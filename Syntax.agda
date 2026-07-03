open import Data.Empty renaming (⊥ to 𝟘) public
open import Data.Nat using (ℕ ; suc) public
open import Data.Fin using (Fin ; zero ; suc) public

Ctx = ℕ
Var = Fin

extend : Ctx → Ctx
extend = suc

infix 10 _≈_
infix 10 _∈_
infix  6 ¬_
infixl 5 _∧_
infix 4 _⇔_

data term (Γ : Ctx) : Set where
  svar : Var Γ → term Γ

data formula (Γ : Ctx) : Set where
  _≈_ : term Γ → term Γ → formula Γ
  _∈_ : term Γ → term Γ → formula Γ
  _∧_ : formula Γ → formula Γ → formula Γ
  _⇔_ : formula Γ → formula Γ → formula Γ
  ¬_ : formula Γ → formula Γ
  all : formula (extend Γ) → formula Γ

mutual
  data Term (C : Set) (Γ : Ctx) : Set where
    svar : Var Γ → Term C Γ
    cvar : C → Term C Γ
    class : Formula C (extend Γ) → Term C Γ

  data Formula (C : Set) (Γ : Ctx) : Set where
    _≈_ : Term C Γ → Term C Γ → Formula C Γ
    _∈_ : Term C Γ → Term C Γ → Formula C Γ
    _∧_ : Formula C Γ → Formula C Γ → Formula C Γ
    _⇔_ : Formula C Γ → Formula C Γ → Formula C Γ
    ¬_ : Formula C Γ → Formula C Γ
    all : Formula C (extend Γ) → Formula C Γ

some : ∀ {Γ} → formula (extend Γ) → formula Γ
some φ = ¬ (all (¬ φ))

exists : ∀ {C Γ} → Formula C (extend Γ) → Formula C Γ
exists Φ = ¬ (all (¬ Φ))

Term₀ : (Γ : Ctx) → Set
Term₀ = Term 𝟘

Formula₀ : (Γ : Ctx) → Set
Formula₀ = Formula 𝟘

inj-term : ∀ {Γ C} → term Γ → Term C Γ
inj-term (svar x) = svar x

inj-formula : ∀ {Γ C} → formula Γ → Formula C Γ
inj-formula (t ≈ u) = (inj-term t) ≈ (inj-term u)
inj-formula (t ∈ u) = (inj-term t) ∈ (inj-term u)
inj-formula (ϕ ∧ ψ) = (inj-formula ϕ) ∧ (inj-formula ψ)
inj-formula (ϕ ⇔ ψ) = (inj-formula ϕ) ⇔ (inj-formula ψ)
inj-formula (¬ ϕ) = ¬ inj-formula ϕ
inj-formula (all ϕ) = all (inj-formula ϕ)