open import Syntax public

open import Relation.Binary.PropositionalEquality using
  (_≡_ ; refl ; cong ; cong₂ ; trans ; sym) renaming (subst to ≡-subst ; subst₂ to ≡-subst₂) public
open import Function.Base using (_∘_) public


-- Renamings of set variables

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
ren-formula r (exists φ) = exists (ren-formula (extend-ren r) φ)

mutual
  ren-Term : ∀ {C Γ Δ} → ren Γ Δ → Term C Γ → Term C Δ
  ren-Term r (svar x) = svar (r x)
  ren-Term r (cvar c) = cvar c
  ren-Term r (class Φ) = class (ren-Formula (extend-ren r) Φ)

  ren-Formula : ∀ {C Γ Δ} → ren Γ Δ → Formula C Γ → Formula C Δ
  ren-Formula r (t ≈ u) = ren-Term r t ≈ ren-Term r u
  ren-Formula r (t ∈ u) = ren-Term r t ∈ ren-Term r u
  ren-Formula r (Φ ∧ Ψ) = ren-Formula r Φ ∧ ren-Formula r Ψ
  ren-Formula r (Φ ⇔ Ψ) = ren-Formula r Φ ⇔ ren-Formula r Ψ
  ren-Formula r (¬ Φ) = ¬ (ren-Formula r Φ)
  ren-Formula r (all Φ) = all (ren-Formula (extend-ren r) Φ)
  ren-Formula r (exists Φ) = exists (ren-Formula (extend-ren r) Φ)

-- Simple renaming of the first de Bruijn index in the context

ren₀ : ∀ {Γ} (x : Var Γ) → ren (extend Γ) Γ
ren₀ x zero = x
ren₀ x (suc y) = y

empty-ren : ∀ {Γ} → ren ⟨⟩ Γ
empty-ren ()

-- Substitutions from class variables to class terms

Subst : Ctx → Set → Set → Set
Subst Γ C D  = C → Term D Γ

comp-rS : ∀ {C D Γ Δ} → ren Γ Δ → Subst Γ C D → Subst Δ C D
comp-rS r σ c = ren-Term r (σ c)

extend-Subst : ∀ {C D Γ} → Subst Γ C D → Subst (extend Γ) C D
extend-Subst σ = comp-rS suc σ

mutual
  Subst-Term : ∀ {C D Γ} → Subst Γ C D → Term C Γ → Term D Γ
  Subst-Term σ (svar x) = svar x
  Subst-Term σ (cvar c) = σ c
  Subst-Term σ (class Φ) = class (Subst-Formula (extend-Subst σ) Φ)

  Subst-Formula : ∀ {C D Γ} → Subst Γ C D → Formula C Γ → Formula D Γ
  Subst-Formula σ (t ≈ u) = (Subst-Term σ t) ≈ (Subst-Term σ u)
  Subst-Formula σ (t ∈ u) = (Subst-Term σ t) ∈ (Subst-Term σ u)
  Subst-Formula σ (Φ ∧ Ψ) = (Subst-Formula σ Φ) ∧ (Subst-Formula σ Ψ)
  Subst-Formula σ (Φ ⇔ Ψ) = (Subst-Formula σ Φ) ⇔ (Subst-Formula σ Ψ)
  Subst-Formula σ (¬ Φ) = ¬ (Subst-Formula σ Φ)
  Subst-Formula σ (all Φ) = all (Subst-Formula (extend-Subst σ) Φ)
  Subst-Formula σ (exists Φ) = exists (Subst-Formula (extend-Subst σ) Φ)

_∘c_ : ∀ {C D E Γ} → Subst Γ D E → Subst Γ C D → Subst Γ C E
(σ' ∘c σ) c = Subst-Term σ' (σ c)

empty-Subst : ∀ {C Γ} → Subst Γ 𝟘 C
empty-Subst ()

lift-Formula₀ : ∀ {C Γ} → Formula₀ Γ → Formula C Γ
lift-Formula₀ = Subst-Formula empty-Subst

-- Simple subtitutions for the main constructs

_[_]f : ∀ {Γ} → formula (extend Γ) → term Γ → formula Γ
φ [ svar x ]f = (ren-formula (ren₀ x)) φ

_[_]F : ∀ {Γ C} → Formula C (extend Γ) → term Γ → Formula C Γ
Φ [ svar x ]F = (ren-Formula (ren₀ x)) Φ


-- Functions for extending terms and formulas

extend-formula-ctx : ∀ {Γ} → formula (extend Γ) → formula (extend (extend Γ))
extend-formula-ctx = ren-formula (extend-ren suc)

extend-Formula-ctx : ∀ {C Γ} → Formula C (extend Γ) → Formula C (extend (extend Γ))
extend-Formula-ctx = ren-Formula (extend-ren suc)

extend-Term-ctx : ∀ {C Γ} → Term C (extend Γ) → Term C (extend (extend Γ))
extend-Term-ctx = ren-Term (extend-ren suc)


-- Function extensionality

postulate
  fun-ext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g


-- Lemmas involving renamings and class variable substitutions

id-ren : ∀ {Γ} → ren Γ Γ
id-ren x = x

extend-preserves-id-ren : ∀ {Γ} → (extend-ren (id-ren {Γ})) ≡ id-ren {extend Γ}
extend-preserves-id-ren = fun-ext λ {zero → refl ; (suc x) → refl}

mutual
  id-ren-Term : ∀ {C Γ} {t : Term C Γ} → (ren-Term id-ren) t ≡ t
  id-ren-Term {t = svar x} = refl
  id-ren-Term {t = cvar c} = refl
  id-ren-Term {t = class Φ} =
    cong
      class
      (trans
        (cong (λ r → ren-Formula r Φ) extend-preserves-id-ren)
        (id-ren-Formula {Φ = Φ}))

  id-ren-Formula : ∀ {C Γ} {Φ : Formula C Γ} → (ren-Formula id-ren) Φ ≡ Φ
  id-ren-Formula {Φ = t ≈ u} = cong₂ _≈_ id-ren-Term id-ren-Term
  id-ren-Formula {Φ = t ∈ u} = cong₂ _∈_ id-ren-Term id-ren-Term
  id-ren-Formula {Φ = Φ ∧ Ψ} = cong₂ _∧_ id-ren-Formula id-ren-Formula
  id-ren-Formula {Φ = Φ ⇔ Ψ} = cong₂ _⇔_ id-ren-Formula id-ren-Formula
  id-ren-Formula {Φ = ¬ Φ} = cong ¬_ id-ren-Formula
  id-ren-Formula {Φ = all Φ} =
    cong
      all
      (trans
        (cong (λ r → ren-Formula r Φ) extend-preserves-id-ren)
        (id-ren-Formula {Φ = Φ}))
  id-ren-Formula {Φ = exists Φ} =
    cong
      exists
      (trans
        (cong (λ r → ren-Formula r Φ) extend-preserves-id-ren)
        (id-ren-Formula {Φ = Φ}))

extend-ren-comp-commute : ∀ {Γ Δ Ω} → (r : ren Γ Δ) (r' : ren Δ Ω) → (extend-ren r') ∘ (extend-ren r) ≡ extend-ren (r' ∘ r)
extend-ren-comp-commute r r' = fun-ext λ {zero → refl ; (suc x) → refl}

mutual
  ren-comp-Term : ∀ {C Γ Δ Ω} {t : Term C Γ} (r : ren Γ Δ) (r' : ren Δ Ω) →
    ren-Term r' (ren-Term r t) ≡ ren-Term (r' ∘ r) t
  ren-comp-Term {t = svar x} r r' = refl
  ren-comp-Term {t = cvar c} r r' = refl
  ren-comp-Term {t = class Φ} r r' =
    cong
      class
      (≡-subst
        (λ f → ren-Formula (extend-ren r') (ren-Formula (extend-ren r) Φ) ≡ ren-Formula f Φ)
        (extend-ren-comp-commute r r')
        (ren-comp-Formula {Φ = Φ} (extend-ren r) (extend-ren r')))

  ren-comp-Formula : ∀ {C Γ Δ Ω} {Φ : Formula C Γ} (r : ren Γ Δ) (r' : ren Δ Ω) →
    ren-Formula r' (ren-Formula r Φ) ≡ ren-Formula (r' ∘ r) Φ
  ren-comp-Formula {Φ = t ≈ u} r r' = cong₂ _≈_ (ren-comp-Term r r') (ren-comp-Term r r')
  ren-comp-Formula {Φ = t ∈ u} r r' = cong₂ _∈_ (ren-comp-Term r r') (ren-comp-Term r r')
  ren-comp-Formula {Φ = Φ ∧ Ψ} r r' = cong₂ _∧_ (ren-comp-Formula r r') (ren-comp-Formula r r')
  ren-comp-Formula {Φ = Φ ⇔ Ψ} r r' = cong₂ _⇔_ (ren-comp-Formula r r') (ren-comp-Formula r r')
  ren-comp-Formula {Φ = ¬ Φ} r r' = cong ¬_ (ren-comp-Formula r r')
  ren-comp-Formula {Φ = all Φ} r r' =
    cong
      all
      (≡-subst
        (λ f → ren-Formula (extend-ren r') (ren-Formula (extend-ren r) Φ) ≡ ren-Formula f Φ)
        (extend-ren-comp-commute r r')
        (ren-comp-Formula {Φ = Φ} (extend-ren r) (extend-ren r')))
  ren-comp-Formula {Φ = exists Φ} r r' =
    cong
      exists
      (≡-subst
        (λ f → ren-Formula (extend-ren r') (ren-Formula (extend-ren r) Φ) ≡ ren-Formula f Φ)
        (extend-ren-comp-commute r r')
        (ren-comp-Formula {Φ = Φ} (extend-ren r) (extend-ren r')))

ren-comp-formula : ∀ {Γ Δ Ω} {φ : formula Γ} (r : ren Γ Δ) (r' : ren Δ Ω) → ren-formula r' (ren-formula r φ) ≡ ren-formula (r' ∘ r) φ
ren-comp-formula {φ = svar x ≈ svar y} r r' = refl
ren-comp-formula {φ = svar x ∈ svar y} r r' = refl
ren-comp-formula {φ = φ ∧ ψ} r r' = cong₂ _∧_ (ren-comp-formula r r') (ren-comp-formula r r')
ren-comp-formula {φ = φ ⇔ ψ} r r' = cong₂ _⇔_ (ren-comp-formula r r') (ren-comp-formula r r')
ren-comp-formula {φ = ¬ φ} r r' = cong ¬_ (ren-comp-formula r r')
ren-comp-formula {φ = all φ} r r' =
  cong
    all
    (≡-subst
      (λ f → ren-formula (extend-ren r') (ren-formula (extend-ren r) φ) ≡ ren-formula f φ)
      (extend-ren-comp-commute r r')
      (ren-comp-formula {φ = φ} (extend-ren r) (extend-ren r')))
ren-comp-formula {φ = exists φ} r r' =
  cong
    exists
    (≡-subst
      (λ f → ren-formula (extend-ren r') (ren-formula (extend-ren r) φ) ≡ ren-formula f φ)
      (extend-ren-comp-commute r r')
      (ren-comp-formula {φ = φ} (extend-ren r) (extend-ren r')))

subst-inj-commute-ren : ∀ {C Γ Δ} {φ : formula (extend Γ)} (r : ren (extend Γ) Δ) →
  ren-Formula {C = C} r (inj-formula φ) ≡ inj-formula (ren-formula r φ)
subst-inj-commute-ren {φ = svar x ≈ svar y} r = refl
subst-inj-commute-ren {φ = svar x ∈ svar y} r = refl
subst-inj-commute-ren {φ = φ ∧ ψ} r = cong₂ _∧_ (subst-inj-commute-ren r) (subst-inj-commute-ren r)
subst-inj-commute-ren {φ = φ ⇔ ψ} r = cong₂ _⇔_ (subst-inj-commute-ren r) (subst-inj-commute-ren r)
subst-inj-commute-ren {φ = ¬ φ} r = cong ¬_ (subst-inj-commute-ren r)
subst-inj-commute-ren {φ = all φ} r = cong all (subst-inj-commute-ren (extend-ren r))
subst-inj-commute-ren {φ = exists φ} r = cong exists (subst-inj-commute-ren (extend-ren r))

subst-inj-commute-ren-zero : ∀ {C Γ} {φ : formula (extend Γ)} {x : Var Γ} →
  ren-Formula {C = C} (ren₀ x) (inj-formula φ) ≡ inj-formula (ren-formula (ren₀ x) φ)
subst-inj-commute-ren-zero {x = x} = subst-inj-commute-ren (ren₀ x)

ren-zero-extend-ctx-id : ∀ {Γ} → (ren₀ {Γ = extend Γ} zero) ∘ (extend-ren suc) ≡ id-ren
ren-zero-extend-ctx-id = fun-ext λ {zero → refl ; (suc x) → refl}

extend-suc-lemma : ∀ {Γ Δ} (r : ren Γ Δ) → (extend-ren suc) ∘ (extend-ren r) ≡ (extend-ren (extend-ren r)) ∘ (extend-ren suc)
extend-suc-lemma r = fun-ext λ {zero → refl ; (suc x) → refl}

renaming-suc-commute : ∀ {Γ Δ} (r : ren Γ Δ) → (extend-ren r) ∘ suc ≡ suc ∘ r
renaming-suc-commute r = fun-ext λ {zero → refl ; (suc x) → refl}

renaming-suc-commute-Term : ∀ {C Γ Δ} {t : Term C Γ} (r : ren Γ Δ) →
  ren-Term (extend-ren r) (ren-Term suc t) ≡ ren-Term suc (ren-Term r t)
renaming-suc-commute-Term {t = t} r =
  trans
    (trans
      (ren-comp-Term suc (extend-ren r))
      (cong (λ r' → ren-Term r' t) (renaming-suc-commute r)))
    (sym (ren-comp-Term r suc))

id-Subst : ∀ {C Γ} → Subst Γ C C
id-Subst c = cvar c

mutual
  id-Subst-Term : ∀ {C Γ} {t : Term C Γ} → Subst-Term id-Subst t ≡ t
  id-Subst-Term {t = svar x} = refl
  id-Subst-Term {t = cvar c} = refl
  id-Subst-Term {t = class Φ} = cong class id-Subst-Formula

  id-Subst-Formula : ∀ {C Γ} {Φ : Formula C Γ} → Subst-Formula id-Subst Φ ≡ Φ
  id-Subst-Formula {Φ = t ≈ u} = cong₂ _≈_ id-Subst-Term id-Subst-Term
  id-Subst-Formula {Φ = t ∈ u} = cong₂ _∈_ id-Subst-Term id-Subst-Term
  id-Subst-Formula {Φ = Φ ∧ Ψ} = cong₂ _∧_ id-Subst-Formula id-Subst-Formula
  id-Subst-Formula {Φ = Φ ⇔ Ψ} = cong₂ _⇔_ id-Subst-Formula id-Subst-Formula
  id-Subst-Formula {Φ = ¬ Φ} = cong ¬_ id-Subst-Formula
  id-Subst-Formula {Γ = Γ} {Φ = all Φ} = cong all id-Subst-Formula
  id-Subst-Formula {Φ = exists Φ} = cong exists id-Subst-Formula

extend-comp-rS-commute : ∀ {C D Γ Δ} (r : ren Γ Δ) (σ : Subst Γ C D) →
  comp-rS (extend-ren r) (extend-Subst σ) ≡ extend-Subst (comp-rS r σ)
extend-comp-rS-commute {C = C} r σ = fun-ext lemma
  where
    lemma : (x : C) →
      comp-rS (extend-ren r) (extend-Subst σ) x ≡ extend-Subst (comp-rS r σ) x
    lemma x = renaming-suc-commute-Term r

mutual
  comp-rS-Term : ∀ {C D Γ Δ} {t : Term C Γ} (σ : Subst Γ C D) (r : ren Γ Δ) →
    ren-Term r (Subst-Term σ t) ≡ Subst-Term (comp-rS r σ) (ren-Term r t)
  comp-rS-Term {t = svar x} σ r = refl
  comp-rS-Term {t = cvar c} σ r = refl
  comp-rS-Term {t = class Φ} σ r =
    cong
      class
      (trans
        (comp-rS-Formula {Φ = Φ} (extend-Subst σ) (extend-ren r))
        (cong
          (λ σ' → Subst-Formula σ' (ren-Formula (extend-ren r) Φ))
          (extend-comp-rS-commute r σ)))

  comp-rS-Formula : ∀ {C D Γ Δ} {Φ : Formula C Γ} (σ : Subst Γ C D) (r : ren Γ Δ) →
    ren-Formula r (Subst-Formula σ Φ) ≡ Subst-Formula (comp-rS r σ) (ren-Formula r Φ)
  comp-rS-Formula {Φ = t ≈ u} σ r = cong₂ _≈_ (comp-rS-Term {t = t} σ r) (comp-rS-Term {t = u} σ r)
  comp-rS-Formula {Φ = t ∈ u} σ r = cong₂ _∈_ (comp-rS-Term {t = t} σ r) (comp-rS-Term {t = u} σ r)
  comp-rS-Formula {Φ = Φ ∧ Ψ} σ r = cong₂ _∧_ (comp-rS-Formula {Φ = Φ} σ r) (comp-rS-Formula {Φ = Ψ} σ r)
  comp-rS-Formula {Φ = Φ ⇔ Ψ} σ r = cong₂ _⇔_ (comp-rS-Formula {Φ = Φ} σ r) (comp-rS-Formula {Φ = Ψ} σ r)
  comp-rS-Formula {Φ = ¬ Φ} σ r = cong ¬_ (comp-rS-Formula {Φ = Φ} σ r)
  comp-rS-Formula {Φ = all Φ} σ r =
    cong
      all
      (trans
        (comp-rS-Formula {Φ = Φ} (extend-Subst σ) (extend-ren r))
        (cong
          (λ σ' → Subst-Formula σ' (ren-Formula (extend-ren r) Φ))
          (extend-comp-rS-commute r σ)))
  comp-rS-Formula {Φ = exists Φ} σ r =
    cong
      exists
      (trans
        (comp-rS-Formula {Φ = Φ} (extend-Subst σ) (extend-ren r))
        (cong
          (λ σ' → Subst-Formula σ' (ren-Formula (extend-ren r) Φ))
          (extend-comp-rS-commute r σ)))

extend-Subst-comp-commute : ∀ {C D E Γ} (σ : Subst Γ C D) (σ' : Subst Γ D E) →
  (extend-Subst σ') ∘c (extend-Subst σ) ≡ extend-Subst (σ' ∘c σ)
extend-Subst-comp-commute {D = D} {Γ = Γ} σ σ' = fun-ext λ c → sym (comp-rS-Term {t = σ c} σ' suc)

mutual
  Subst-comp-Term : ∀ {C D E Γ} {t : Term C Γ} (σ : Subst Γ C D) (σ' : Subst Γ D E) →
    Subst-Term σ' (Subst-Term σ t) ≡ Subst-Term (σ' ∘c σ) t
  Subst-comp-Term {t = svar x} σ σ' = refl
  Subst-comp-Term {t = cvar c} σ σ' = refl
  Subst-comp-Term {t = class Φ} σ σ' =
    cong
      class
      (trans
        (Subst-comp-Formula (extend-Subst σ) (extend-Subst σ'))
        (cong (λ σ → Subst-Formula σ Φ) (extend-Subst-comp-commute σ σ')))

  Subst-comp-Formula : ∀ {C D E Γ} {Φ : Formula C Γ} (σ : Subst Γ C D) (σ' : Subst Γ D E) →
    Subst-Formula σ' (Subst-Formula σ Φ) ≡ Subst-Formula (σ' ∘c σ) Φ
  Subst-comp-Formula {Φ = t ≈ u} σ σ' = cong₂ _≈_ (Subst-comp-Term {t = t} σ σ') (Subst-comp-Term {t = u} σ σ')
  Subst-comp-Formula {Φ = t ∈ u} σ σ' = cong₂ _∈_ (Subst-comp-Term {t = t} σ σ') (Subst-comp-Term {t = u} σ σ')
  Subst-comp-Formula {Φ = Φ ∧ Ψ} σ σ' = cong₂ _∧_ (Subst-comp-Formula σ σ') (Subst-comp-Formula σ σ')
  Subst-comp-Formula {Φ = Φ ⇔ Ψ} σ σ' = cong₂ _⇔_ (Subst-comp-Formula σ σ') (Subst-comp-Formula σ σ')
  Subst-comp-Formula {Φ = ¬ Φ} σ σ' = cong ¬_ (Subst-comp-Formula σ σ')
  Subst-comp-Formula {Φ = all Φ} σ σ' =
    cong
      all
      (trans
        (Subst-comp-Formula (extend-Subst σ) (extend-Subst σ'))
        (cong (λ σ → Subst-Formula σ Φ) (extend-Subst-comp-commute σ σ')))
  Subst-comp-Formula {Φ = exists Φ} σ σ' =
    cong
      exists
      (trans
        (Subst-comp-Formula (extend-Subst σ) (extend-Subst σ'))
        (cong (λ σ → Subst-Formula σ Φ) (extend-Subst-comp-commute σ σ')))

extend-empty-eq : ∀ {C Γ} → extend-Subst {D = C} (empty-Subst {Γ = Γ}) ≡ empty-Subst {Γ = extend Γ}
extend-empty-eq = fun-ext λ ()

Subst-empty-id : ∀ {C Γ} {φ : formula Γ} → Subst-Formula {D = C} empty-Subst (inj-formula φ) ≡ inj-formula φ
Subst-empty-id {φ = svar x ≈ svar y} = refl
Subst-empty-id {φ = svar x ∈ svar y} = refl
Subst-empty-id {φ = φ ∧ ψ} = cong₂ _∧_ Subst-empty-id Subst-empty-id
Subst-empty-id {φ = φ ⇔ ψ} = cong₂ _⇔_ Subst-empty-id Subst-empty-id
Subst-empty-id {φ = ¬ φ} = cong ¬_ Subst-empty-id
Subst-empty-id {φ = all φ} =
  cong
    all
    (trans
      (cong (λ σ → Subst-Formula σ (inj-formula φ)) extend-empty-eq)
      Subst-empty-id)
Subst-empty-id {φ = exists φ} =
  cong
    exists
    (trans
      (cong (λ σ → Subst-Formula σ (inj-formula φ)) extend-empty-eq)
      Subst-empty-id)

record Sbs (C : Set) (Γ : Ctx) (D : Set) (Δ : Ctx) : Set where
  field
    sbs-cls : C → Term D Δ
    sbs-set : ren Γ Δ