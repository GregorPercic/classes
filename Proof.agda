open import Data.List hiding (all)

open import Syntax
open import Substitutions
open import Theory

data mem {X : Set} : X → List X → Set where
  here : ∀ {x xs} → mem x (x ∷ xs)
  there : ∀ {x y xs} → mem x xs → mem x (y ∷ xs)

weaken : ∀ {C Γ} → Formula C Γ → Formula C (extend Γ)
weaken = ren-Formula suc

data Proof (T : Theory) {C : Set} : {Γ : Ctx} → List (Formula C Γ) → Formula C Γ → Set₂ where
  axiom :
    ∀ {Γ} {Hyp} (i : thy-idx T)
    (σ : Subst Γ (thy-cls T i) C)
    (r : ren (thy-ctx T i) Γ) →
    Proof T Hyp (Subst-Formula σ (ren-Formula r (thy-axi T i)))

  hyp : ∀ {Γ} {Hyp} {Φ : Formula C Γ} →
    mem Φ Hyp →
    -------------
    Proof T Hyp Φ

  -- we don't need this rule for the eliminability theorem
  -- all-intro :
  --   ∀ {Γ} {Φ : Formula C (extend Γ)} →
  --   Proof T Φ →
  --   ---------------
  --   Proof T (all Φ)

  ⇔-refl : ∀ {Γ} {Hyp} {Φ : Formula C Γ} → Proof T Hyp (Φ ⇔ Φ)

  ∧-intro : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp Φ →
    Proof T Hyp Ψ →
    ----------------
    Proof T Hyp (Φ ∧ Ψ )

  ⇒-intro : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T (Φ ∷ Hyp) Ψ →
    --------------------
    Proof T Hyp (Φ ⇒ Ψ)

  exists-elim : ∀ {Γ} {Hyp} {Φ : Formula C (extend Γ)} {Ψ : Formula C Γ} →
    Proof T Hyp (exists Φ) →
    Proof T (Φ ∷ map weaken Hyp) (ren-Formula suc Ψ) →
    -----------------------------------------
    Proof T Hyp Ψ

  all-elim : ∀ {Γ} {Hyp} {Φ : Formula C (extend Γ)} {t : term Γ} →
    Proof T Hyp (all Φ) →
    ---------------------
    Proof T Hyp (Φ [ t ]F)

  ∧-cong : ∀ {Γ} {Hyp} {Φ Φ' Ψ Ψ' : Formula C Γ} →
    Proof T Hyp (Φ ⇔ Φ') →
    Proof T Hyp (Ψ ⇔ Ψ') →
    -------------------------
    Proof T Hyp (Φ ∧ Ψ ⇔ Φ' ∧ Ψ')

  ⇔-cong : ∀ {Γ} {Hyp} {Φ Φ' Ψ Ψ' : Formula C Γ} →
    Proof T Hyp (Φ ⇔ Φ') →
    Proof T Hyp (Ψ ⇔ Ψ') →
    ------------------------------
    Proof T Hyp ((Φ ⇔ Ψ) ⇔ (Φ' ⇔ Ψ'))

  ¬-cong : ∀ {Γ} {Hyp} {Φ Φ' : Formula C Γ} →
    Proof T Hyp (Φ ⇔ Φ') →
    --------------------
    Proof T Hyp (¬ Φ ⇔ ¬ Φ')

  all-cong : ∀ {Γ} {Hyp} {Φ Φ' : Formula C (extend Γ)} →
    Proof T (map weaken Hyp) (Φ ⇔ Φ') →
    -------------------------
    Proof T Hyp (all Φ ⇔ all Φ')

  ⇔-trans : ∀ {Γ} {Hyp} {Φ Φ' Φ'' : Formula C Γ} →
    Proof T Hyp (Φ ⇔ Φ') →
    Proof T Hyp (Φ' ⇔ Φ'') →
    ---------------------
    Proof T Hyp (Φ ⇔ Φ'')

  exists-cong : ∀ {Γ} {Hyp} {Φ Φ' : Formula C (extend Γ)} →
    Proof T (map weaken Hyp) (Φ ⇔ Φ') →
    ------------------------------
    Proof T Hyp (exists Φ ⇔ exists Φ')

axiom-ren :
  ∀ {T Γ} (i : thy-idx T) {Hyp}
  (r : ren (thy-ctx T i) Γ) →
  -------------------------------------
  Proof T {C = thy-cls T i} {Γ = Γ} Hyp (ren-Formula r (thy-axi T i))
axiom-ren {T = T} i {Hyp = Hyp} r = ≡-subst (λ Ξ → Proof T Hyp Ξ) (id-Subst-Formula) (axiom i id-Subst r)

axiom-Subst :
  ∀ {T C} (i : thy-idx T) {Hyp}
  (σ : Subst (thy-ctx T i) (thy-cls T i) C) →
  -------------------------------------------
  Proof T {C = C} {Γ = thy-ctx T i} Hyp (Subst-Formula σ (thy-axi T i))
axiom-Subst {T = T} i {Hyp = Hyp} σ = ≡-subst (λ Ξ → Proof T Hyp (Subst-Formula σ Ξ)) id-ren-Formula (axiom i σ id-ren)

axiom-exact :
  ∀ {T} (i : thy-idx T) {Hyp} →
  -----------------------
  Proof T Hyp (thy-axi T i)
axiom-exact {T = T} i {Hyp = Hyp} = ≡-subst (λ Ξ → Proof T Hyp Ξ) id-ren-Formula (axiom-ren i id-ren)

-- ren-Proof : ∀ {T C Γ Δ Hyp } {Φ : Formula C Γ} (r : ren Γ Δ) → Proof T Hyp Φ → Proof T (map (ren-Formula r) Hyp) (ren-Formula r Φ)
-- ren-Proof {T = T} {Hyp = Hyp} r (axiom i σ r') =
--   ≡-subst
--     (λ Ξ → Proof T Hyp Ξ)
--     (sym
--       (trans
--         (comp-rS-Formula {Φ = ren-Formula r' (thy-axi T i)} σ r)
--         (cong (λ Ξ → Subst-Formula (comp-rS r σ) Ξ) (ren-comp-Formula r' r))))
--     (axiom i (comp-rS r σ) (r ∘ r'))
-- ren-Proof r ⇔-refl = ⇔-refl
-- ren-Proof r (∧-intro p q) = ∧-intro (ren-Proof r p) (ren-Proof r q)
-- ren-Proof r (∧-cong p p') = ∧-cong (ren-Proof r p) (ren-Proof r p')
-- ren-Proof r (⇔-cong p p') = ⇔-cong (ren-Proof r p) (ren-Proof r p')
-- ren-Proof r (¬-cong p) = ¬-cong (ren-Proof r p)
-- ren-Proof r (all-cong p) = all-cong (ren-Proof (extend-ren r) p)
-- ren-Proof r (⇔-trans p p') = ⇔-trans (ren-Proof r p) (ren-Proof r p')
-- ren-Proof r (exists-cong p) = exists-cong (ren-Proof (extend-ren r) p)

-- Subst-Proof : ∀ {T C D Γ Hyp} {Φ : Formula C Γ} (σ : Subst Γ C D) → Proof T Hyp Φ → Proof T Hyp (Subst-Formula σ Φ)
-- Subst-Proof {T = T} {Hyp = Hyp} σ (axiom i σ' r) =
--   ≡-subst (λ Ξ → Proof T Hyp Ξ) (sym (Subst-comp-Formula σ' σ)) (axiom i (σ ∘c σ') r)
-- Subst-Proof σ ⇔-refl = ⇔-refl
-- Subst-Proof σ (∧-intro p p') = ∧-intro (Subst-Proof σ p) (Subst-Proof σ p')
-- Subst-Proof σ (∧-cong p p') = ∧-cong (Subst-Proof σ p) (Subst-Proof σ p')
-- Subst-Proof σ (⇔-cong p p') = ⇔-cong (Subst-Proof σ p) (Subst-Proof σ p')
-- Subst-Proof σ (¬-cong p) = ¬-cong (Subst-Proof σ p)
-- Subst-Proof σ (all-cong p) = all-cong (Subst-Proof (extend-Subst σ) p)
-- Subst-Proof σ (⇔-trans p p') = ⇔-trans (Subst-Proof σ p) (Subst-Proof σ p')
-- Subst-Proof σ (exists-cong p) = exists-cong (Subst-Proof (extend-Subst σ) p)

-- subst-dist-⇔ : ∀ {T C Γ Hyp} {Φ Ψ : Formula C (extend Γ)} (x : Var Γ) → Proof T Hyp (Φ ⇔ Ψ) → Proof T Hyp (Φ [ svar x ]F ⇔ Ψ [ svar x ]F)
-- subst-dist-⇔ x p = ren-Proof (ren₀ x) p -- all-elim (all-intro p) ; if we can cope with having all-elim

-- eq-to-⇔ : ∀ {Γ C T Hyp} {Φ Ψ : Formula Γ C} → Φ ≡ Ψ → Proof T Hyp (Φ ⇔ Ψ)
-- eq-to-⇔ refl = ⇔-refl

-- ⇔-∈-subst : ∀ {Γ} {Hyp} {Φ : Formula₀ (extend Γ)} →
--   Proof CT (svar zero ∈ (class (extend-Formula-ctx Φ)) ⇔ (extend-Formula-ctx Φ) [ svar zero ]F)
-- ⇔-∈-subst {Γ} {Φ} = axiom-exact (set∈class 𝟘 (extend Γ) zero (extend-Formula-ctx Φ))
