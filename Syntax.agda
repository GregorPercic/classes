open import Data.Empty renaming (⊥ to 𝟘) public
open import Data.Nat using (ℕ ; suc) public
open import Data.Fin using (Fin ; zero ; suc) public
open import Data.List hiding (all) renaming (_∷_ to _∷l_ ; _++_ to _++l_) public

Ctx = ℕ
Var = Fin

⟨⟩ = 0 -- empty context

Fin-with-𝟘 : ℕ → Set
Fin-with-𝟘 ℕ.zero = 𝟘
Fin-with-𝟘 (suc n) = Fin (suc n)

extend : Ctx → Ctx
extend = suc

infix 10 _≈_
infix 10 _∈_
infixl 5 _∧_
infixr 4 _⇒_
infix 3 _⇔_

data term (Γ : Ctx) : Set where
  svar : Var Γ → term Γ

data formula (Γ : Ctx) : Set where
  ⊥ : formula Γ
  _≈_ : term Γ → term Γ → formula Γ
  _∈_ : term Γ → term Γ → formula Γ
  _∧_ : formula Γ → formula Γ → formula Γ
  _⇒_ : formula Γ → formula Γ → formula Γ
  _⇔_ : formula Γ → formula Γ → formula Γ
  all : formula (extend Γ) → formula Γ
  exists : formula (extend Γ) → formula Γ

mutual
  data Term (C : Set) (Γ : Ctx) : Set where
    svar : Var Γ → Term C Γ
    cvar : C → Term C Γ
    class : Formula C (extend Γ) → Term C Γ

  data Formula (C : Set) (Γ : Ctx) : Set where
    ⊥ : Formula C Γ
    _≈_ : Term C Γ → Term C Γ → Formula C Γ
    _∈_ : Term C Γ → Term C Γ → Formula C Γ
    _∧_ : Formula C Γ → Formula C Γ → Formula C Γ
    _⇒_ : Formula C Γ → Formula C Γ → Formula C Γ
    _⇔_ : Formula C Γ → Formula C Γ → Formula C Γ
    all : Formula C (extend Γ) → Formula C Γ
    exists : Formula C (extend Γ) → Formula C Γ

Term₀ : (Γ : Ctx) → Set
Term₀ = Term 𝟘

Formula₀ : (Γ : Ctx) → Set
Formula₀ = Formula 𝟘

inj-term : ∀ {Γ C} → term Γ → Term C Γ
inj-term (svar x) = svar x

inj-formula : ∀ {Γ C} → formula Γ → Formula C Γ
inj-formula ⊥ = ⊥
inj-formula (t ≈ u) = (inj-term t) ≈ (inj-term u)
inj-formula (t ∈ u) = (inj-term t) ∈ (inj-term u)
inj-formula (φ ∧ ψ) = (inj-formula φ) ∧ (inj-formula ψ)
inj-formula (φ ⇒ ψ) = (inj-formula φ) ⇒ (inj-formula ψ)
inj-formula (φ ⇔ ψ) = (inj-formula φ) ⇔ (inj-formula ψ)
inj-formula (all φ) = all (inj-formula φ)
inj-formula (exists φ) = exists (inj-formula φ)

_∷_ : {X : Set} → List X → X → List X
tl ∷ h = h ∷l tl

_++_ : {X : Set} → List X → List X → List X
l ++ l' = l' ++l l

data _∋_ {X : Set} : List X → X → Set where
  here : ∀ {x xs} → (xs ∷ x) ∋ x
  there : ∀ {x y xs} → xs ∋ x → (xs ∷ y) ∋ x