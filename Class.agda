open import Data.Empty renaming (⊥ to 𝟘)
open import Data.Nat
open import Data.Fin
open import Data.Product

module Class where
  Ctx = ℕ
  ⟨⟩ = 0 -- empty context

  Var = Fin

  Ren : Ctx → Ctx → Set
  Ren Γ Δ = Var Γ → Var Δ

  extend : Ctx → Ctx
  extend = suc

  extend-Ren : ∀ {Γ Δ} → Ren Γ Δ → Ren (extend Γ) (extend Δ)
  extend-Ren ρ zero = zero
  extend-Ren ρ (suc x) = suc (ρ x)

  infix 10 _≈_
  infix 10 _∈_
  infix  6 ¬_
  infixl 5 _∧_
  infix 3 _⇔_

  data term (Γ : Ctx) : Set where
    svar : Var Γ → term Γ

  actR-term : ∀ {Γ Δ} → Ren Γ Δ → term Γ → term Δ
  actR-term ρ (svar x) = svar (ρ x)

  data formula (Γ : Ctx) : Set where
    _≈_ : term Γ → term Γ → formula Γ
    _∈_ : term Γ → term Γ → formula Γ
    _∧_ : formula Γ → formula Γ → formula Γ
    _⇔_ : formula Γ → formula Γ → formula Γ
    ¬_ : formula Γ → formula Γ
    all : formula (extend Γ) → formula Γ

  actR-formula : ∀ {Γ Δ} → Ren Γ Δ → formula Γ → formula Δ
  actR-formula r (t ≈ u) = actR-term r t ≈ actR-term r u
  actR-formula r (t ∈ u) = actR-term r t ∈ actR-term r u
  actR-formula r (φ ∧ ψ) = actR-formula r φ ∧ actR-formula r ψ
  actR-formula r (φ ⇔ ψ) = actR-formula r φ ⇔ actR-formula r ψ
  actR-formula r (¬ φ) = ¬ (actR-formula r φ)
  actR-formula r (all φ) = all (actR-formula (extend-Ren r) φ)

  Ren-bind-zero : ∀ {Γ} → Ren Γ (extend Γ)
  Ren-bind-zero zero = zero
  Ren-bind-zero (suc x) = suc (suc x)

  extend-formula : ∀ {Γ} → formula Γ → formula (extend Γ)
  extend-formula = actR-formula suc

  extend-formula-bind-zero : ∀ {Γ} → formula Γ → formula (extend Γ)
  extend-formula-bind-zero = actR-formula Ren-bind-zero

  some : ∀ {Γ} → formula (extend Γ) → formula Γ
  some φ = ¬ (all (¬ φ))

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

  mutual
    actR-Term : ∀ {C Γ Δ} → Ren Γ Δ → Term C Γ → Term C Δ
    actR-Term r (svar x) = svar (r x)
    actR-Term r (cvar A) = cvar A
    actR-Term r (class Φ) = class (actR-Formula (extend-Ren r) Φ)

    actR-Formula : ∀ {C Γ Δ} → Ren Γ Δ → Formula C Γ → Formula C Δ
    actR-Formula r (t ≈ u) = actR-Term r t ≈ actR-Term r u
    actR-Formula r (t ∈ u) = actR-Term r t ∈ actR-Term r u
    actR-Formula r (Φ ∧ Ψ) = actR-Formula r Φ ∧ actR-Formula r Ψ
    actR-Formula r (Φ ⇔ Ψ) = actR-Formula r Φ ⇔ actR-Formula r Ψ
    actR-Formula r (¬ Φ) = ¬ (actR-Formula r Φ)
    actR-Formula r (all Φ) = all (actR-Formula (extend-Ren r) Φ)

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

  Subst : Ctx → Set → Set → Set
  Subst Γ C D  = C → Term D Γ

  subst : Ctx → Ctx → Set
  subst Γ Δ = Var Γ → term Δ

  -- General substitution
  record Sbs (C : Set) (Γ : Ctx) (D : Set) (Δ : Ctx) : Set where
    field
      sbs-cls : C → Term D Δ
      sbs-set : Var Γ → term Δ

  extend-term : ∀ {Γ} → term Γ → term (extend Γ)
  extend-term = actR-term suc

  -- is this correct?
  extend-subst : ∀ {Γ Δ} → subst Γ Δ → subst (extend Γ) (extend Δ)
  extend-subst ρ zero = svar zero
  extend-subst ρ (suc x) = extend-term (ρ x)

  actf : ∀ {Γ Δ} → subst Γ Δ → formula Γ → formula Δ
  actf ρ (svar x ≈ svar y) = ρ x ≈ ρ y
  actf ρ (svar x ∈ svar y) = ρ x ∈ ρ y
  actf ρ (φ ∧ ψ) = actf ρ φ ∧ actf ρ ψ
  actf ρ (φ ⇔ ψ) = actf ρ φ ⇔ actf ρ ψ
  actf ρ (¬ φ) = ¬ (actf ρ φ)
  actf ρ (all φ) = all (actf (extend-subst ρ) φ)

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

  -- useless, because we are using renamings instead
  -- lift-T-act : ∀ {C Γ} → Term C ⟨⟩ → Term C Γ
  -- lift-T-act t = actT (λ ()) t

  compRS : ∀ {Γ Δ C D} → Ren Γ Δ → Subst Γ C D → Subst Δ C D
  compRS r σ x = actR-Term r (σ x)

  extend-Subst : ∀ {Γ C D} → Subst Γ C D → Subst (extend Γ) C D
  extend-Subst σ = compRS suc σ

  mutual
    ActT : ∀ {C D : Set} {Γ} → Subst Γ C D → Term C Γ → Term D Γ
    ActT σ (svar x) = svar x
    ActT σ (cvar c) = σ c
    ActT σ (class Φ) = class (ActF (extend-Subst σ) Φ)

    ActF : ∀ {C D : Set} {Γ} → Subst  Γ C D → Formula C Γ → Formula D Γ
    ActF σ (t ≈ u) = (ActT σ t) ≈ (ActT σ u)
    ActF σ (t ∈ u) = (ActT σ t) ∈ (ActT σ u)
    ActF σ (Φ ∧ Ψ) = (ActF σ Φ) ∧ (ActF σ Ψ)
    ActF σ (Φ ⇔ Ψ) = (ActF σ Φ) ⇔ (ActF σ Ψ)
    ActF σ (¬ Φ) = ¬ (ActF σ Φ)
    ActF {Γ = Γ} σ (all Φ) = all (ActF (extend-Subst σ) Φ)

  -- useless, because we are using renamings instead
  -- lift-T-Act : ∀ {C Γ} → Term₀ Γ → Term C Γ
  -- lift-T-Act t = ActT (λ ()) t

  _[_] : ∀ {Γ C} → Formula C (extend Γ) → term Γ → Formula C Γ
  Φ [ t ] = actF (subst₀ t) Φ

  _⟦_⟧ : ∀ {Γ} → formula (extend Γ) → term Γ → formula Γ
  φ ⟦ t ⟧ = actf (subst₀ t) φ

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
      (σ : Subst Γ (thy-cls T i) C)
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

  ActP : ∀ {T C D Γ} {Φ : Formula C Γ} (σ : Subst Γ C D) → Proof T Φ → Proof T (ActF σ Φ)
  ActP σ p = {!!}

  -- useless, because we are using renamings instead
  -- subst-suc : ∀ {Γ} → subst Γ (extend Γ)
  -- subst-suc x = svar (suc x)

  extend-Term : ∀ {Γ C} → Term C Γ → Term C (extend Γ)
  extend-Term = actR-Term suc

  elim : ∀ {Γ} → Formula₀ Γ → formula Γ
  elim (svar x ≈ svar y) = svar x ≈ svar y
  elim (svar x ≈ class Φ) = all (svar zero ∈ svar (suc x) ⇔ elim Φ)
  elim (class Φ ≈ svar x) = all (elim Φ ⇔ svar zero ∈ svar (suc x))
  elim (class Φ ≈ class Ψ) = all (elim Φ ⇔ elim Ψ)
  elim (svar x ∈ svar y) = svar x ∈ svar y
  elim (svar x ∈ class Φ) =  (elim Φ) ⟦ svar x ⟧
  elim (class Φ ∈ svar x) = some ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-bind-zero (elim Φ))) ∧ svar zero ∈ svar (suc x))
  elim (class Φ ∈ class Ψ) = some ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-bind-zero (elim Φ))) ∧ elim Ψ)
  elim (Φ ∧ Ψ) = elim Φ ∧ elim Ψ
  elim (Φ ⇔ Ψ) = elim Φ ⇔ elim Ψ
  elim (¬ Φ) = ¬ (elim Φ)
  elim (all Φ) = all (elim Φ)

  main-theorem : ∀ {Γ} (Φ : Formula 𝟘 Γ) → Proof CT (Φ ⇔ (inj-formula (elim Φ)))
  main-theorem Φ = {!!}

  eliminability : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → Proof CT (ActF σ Φ ⇔ inj-formula (elim (ActF σ Φ)))
  eliminability C Φ σ  = main-theorem (ActF σ Φ)

  corollary : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → ∃[ φ ] Proof CT (ActF σ Φ ⇔ inj-formula φ)
  corollary C Φ σ = elim (ActF σ Φ) , eliminability C Φ σ
