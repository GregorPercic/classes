open import Data.Empty renaming (⊥ to 𝟘)
open import Data.Nat
open import Data.Fin
open import Data.Product

module Class where
  Ctx = ℕ
  ⟨⟩ = 0 -- empty context

  Var = Fin

  extend : Ctx → Ctx
  extend = suc

  infix 10 _≈_
  infix 10 _∈_
  infix  6 ¬_
  infixl 5 _∧_
  infix 3 _⇔_

  data term (Γ : Ctx) : Set where
    svar : Var Γ → term Γ

  data formula (Γ : Ctx) : Set where
    _≈_ : term Γ → term Γ → formula Γ
    _∈_ : term Γ → term Γ → formula Γ
    _∧_ : formula Γ → formula Γ → formula Γ
    _⇔_ : formula Γ → formula Γ → formula Γ
    ¬_ : formula Γ → formula Γ
    all : formula (extend Γ) → formula Γ

  exists-formula : ∀ {Γ} → formula (extend Γ) → formula Γ
  exists-formula φ = ¬ (all (¬ φ))

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

  inj-term : ∀ {Γ C} → term Γ → Term C Γ
  inj-term (svar x) = svar x

  inj-formula : ∀ {Γ C} → formula Γ → Formula C Γ
  inj-formula (t ≈ u) = (inj-term t) ≈ (inj-term u)
  inj-formula (t ∈ u) = (inj-term t) ∈ (inj-term u)
  inj-formula (ϕ ∧ ψ) = (inj-formula ϕ) ∧ (inj-formula ψ)
  inj-formula (ϕ ⇔ ψ) = (inj-formula ϕ) ⇔ (inj-formula ψ)
  inj-formula (¬ ϕ) = ¬ inj-formula ϕ
  inj-formula (all ϕ) = all (inj-formula ϕ)

  Sentence : (C : Set) → Set
  Sentence C = Formula C ⟨⟩

  Term₀ : (Γ : Ctx) → Set
  Term₀ = Term 𝟘

  Formula₀ : (Γ : Ctx) → Set
  Formula₀ = Formula 𝟘

  Subst : Set → Set → Set
  Subst C D = C → Term D ⟨⟩

  subst : Ctx → Ctx → Set
  subst Γ Δ = Var Γ → term Δ

  -- General substitution
  record Sbs (C : Set) (Γ : Ctx) (D : Set) (Δ : Ctx) : Set where
    field
      sbs-cls : C → Term D Δ
      sbs-set : Var Γ → term Δ

  extend-term : ∀ {Γ} → term Γ → term (extend Γ)
  extend-term (svar x) = svar (suc x)

  -- is this correct?
  extend-subst : ∀ {Γ Δ} → subst Γ Δ → subst (extend Γ) (extend Δ)
  extend-subst ρ zero = svar zero
  extend-subst ρ (suc x) = extend-term (ρ x)

  mutual
    actT : ∀ {C : Set} {Γ Δ} → subst Γ Δ → Term C Γ → Term C Δ
    actT ρ (svar x) = inj-term (ρ x)
    actT ρ (cvar c) = cvar c
    actT ρ (class Φ) = class (actF (extend-subst ρ) Φ) -- need to skip bound variable x in { x | Φ }

    actF : ∀ {C : Set} {Γ Δ} → subst Γ Δ → Formula C Γ → Formula C Δ
    actF ρ (t ≈ u) = (actT ρ t) ≈ (actT ρ u)
    actF ρ (t ∈ u) = (actT ρ t) ∈ (actT ρ u)
    actF ρ (Φ ∧ Ψ) = (actF ρ Φ) ∧ (actF ρ Ψ)
    actF ρ (Φ ⇔ Ψ) = (actF ρ Φ) ⇔ (actF ρ Ψ)
    actF ρ (¬ Φ) = ¬ (actF ρ Φ)
    actF ρ (all Φ) = all (actF (extend-subst ρ) Φ) -- need to skip bound variable x in ∀x.Φ

  subst₀ : ∀ {Γ : Ctx} → term Γ → subst (extend Γ) Γ
  subst₀ t zero = t
  subst₀ t (suc x) = svar x

  lift-T-act : ∀ {C Γ} → Term C ⟨⟩ → Term C Γ
  lift-T-act t = actT (λ ()) t

  mutual
    ActT : ∀ {C D : Set} {Γ} → Subst C D → Term C Γ → Term D Γ
    ActT σ (svar x) = svar x
    ActT σ (cvar c) = lift-T-act (σ c) -- need to lift into Γ
    ActT σ (class Φ) = class (ActF σ Φ)

    ActF : ∀ {C D : Set} {Γ} → Subst C D → Formula C Γ → Formula D Γ
    ActF σ (t ≈ u) = (ActT σ t) ≈ (ActT σ u)
    ActF σ (t ∈ u) = (ActT σ t) ∈ (ActT σ u)
    ActF σ (Φ ∧ Ψ) = (ActF σ Φ) ∧ (ActF σ Ψ)
    ActF σ (Φ ⇔ Ψ) = (ActF σ Φ) ⇔ (ActF σ Ψ)
    ActF σ (¬ Φ) = ¬ (ActF σ Φ)
    ActF σ (all Φ) = all (ActF σ Φ)

  lift-T-Act : ∀ {C Γ} → Term₀ Γ → Term C Γ
  lift-T-Act t = ActT (λ ()) t

  _[_] : ∀ {Γ C} → Formula C (extend Γ) → term Γ → Formula C Γ
  Φ [ t ] = actF (subst₀ t) Φ
 
  exists : ∀ {C Γ} → Formula C (extend Γ) → Formula C Γ
  exists Φ = ¬ (all (¬ Φ))

  record Theory : Set₁ where
    field
      thy-idx : Set -- axiom names
      thy-cls : thy-idx → Set -- class variables appearing in the axiom
      thy-ctx : thy-idx → Ctx -- set variables appearing in the axiom
      thy-axi : ∀ (i : thy-idx) → Formula (thy-cls i) (thy-ctx i)

  open Theory

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
  thy-ctx CT class∈class = 0
  thy-ctx CT class≈class = 0

  thy-axi CT (set∈class n Γ y Φ) = svar y ∈ class Φ ⇔ Φ [ svar y ]
  thy-axi CT class∈class = cvar A ∈ cvar B ⇔ exists (svar zero ≈ cvar A ∧ svar zero ∈ cvar B) -- perhaps a bad formulation
  thy-axi CT class≈class = cvar A ≈ cvar B ⇔ all (svar zero ∈ cvar A ⇔ svar zero ∈ cvar B)

  -- The notion of proof: maybe notation "p : T ⊢ ϕ" means p is a proof of Φ in T
  data Proof (T : Theory) {C : Set} : {Γ : Ctx} → Formula C Γ → Set where
    axiom :
      ∀ {Γ} (i : thy-idx T)
      (σ : Subst (thy-cls T i) C)
      (ρ : subst (thy-ctx T i) Γ) →
      Proof T (ActF σ (actF ρ (thy-axi T i)))

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

  actP : ∀ {T C Γ Δ} {Φ : Formula C Γ} (ρ : subst Γ Δ) → Proof T Φ → Proof T (actF ρ Φ)
  actP ρ p = {!!}

  ActP : ∀ {T C D Γ} {Φ : Formula C Γ} (σ : Subst C D) → Proof T Φ → Proof T (ActF σ Φ)
  ActP σ p = {!!}

  subst-suc : ∀ {Γ} → subst Γ (extend Γ)
  subst-suc x = svar (suc x)

  extend-Term : ∀ {Γ C} → Term C Γ → Term C (extend Γ)
  extend-Term t = actT subst-suc t

  elim : ∀ {Γ} → Formula 𝟘 Γ → formula Γ
  elim (svar x ≈ svar y) = svar x ≈ svar y
  elim (svar x ≈ class Φ) = all (svar zero ∈ svar (suc x) ⇔ elim Φ) -- ?
  elim (class Φ ≈ svar x) = all (elim Φ ⇔ svar zero ∈ svar (suc x)) -- ?
  elim (class Φ ≈ class Ψ) = all (elim Φ ⇔ elim Ψ)
  elim (svar x ∈ svar y) = svar x ∈ svar y
  elim (svar x ∈ class Φ) = elim (Φ [ svar x ]) -- ?
  elim (class Φ ∈ svar x) = exists-formula (elim (svar zero ≈ extend-Term (class Φ)) ∧ svar zero ∈ svar (suc x))
  elim (class Φ ∈ class Ψ) = exists-formula (elim (svar zero ≈ extend-Term (class Φ)) ∧ elim Ψ)
  elim (Φ ∧ Ψ) = elim Φ ∧ elim Ψ
  elim (Φ ⇔ Ψ) = elim Φ ⇔ elim Ψ
  elim (¬ Φ) = ¬ (elim Φ)
  elim (all Φ) = all (elim Φ) -- ?

  main-theorem : ∀ {Γ} (Φ : Formula 𝟘 Γ) → Proof CT (Φ ⇔ (inj-formula (elim Φ)))
  main-theorem Φ = {!!}

  eliminability : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst C 𝟘) → Proof CT (ActF σ Φ ⇔ inj-formula (elim (ActF σ Φ)))
  eliminability C Φ σ  = main-theorem (ActF σ Φ)

  corollary : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst C 𝟘) → ∃[ φ ] Proof CT (ActF σ Φ ⇔ inj-formula φ)
  corollary C Φ σ = elim (ActF σ Φ) , eliminability C Φ σ