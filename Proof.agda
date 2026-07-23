open import Syntax
open import Substitutions
open import Theory


data Proof (T : Theory) {C : Set} : {Γ : Ctx} → Formula C Γ → Set₂ where
  axiom :
    ∀ {Γ} (i : thy-idx T)
    (σ : Subst Γ (thy-cls T i) C)
    (r : ren (thy-ctx T i) Γ) →
    Proof T (Subst-Formula σ (ren-Formula r (thy-axi T i)))

  -- we don't need this rule for the eliminability theorem
  -- all-intro :
  --   ∀ {Γ} {Φ : Formula C (extend Γ)} →
  --   Proof T Φ →
  --   ---------------
  --   Proof T (all Φ)

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

axiom-ren : 
  ∀ {T Γ} (i : thy-idx T)
  (r : ren (thy-ctx T i) Γ) →
  -------------------------------------
  Proof T {C = thy-cls T i} {Γ = Γ} (ren-Formula r (thy-axi T i))
axiom-ren {T = T} i r = ≡-subst (λ Ξ → Proof T Ξ) (id-Subst-Formula) (axiom i id-Subst r)

axiom-Subst :
  ∀ {T C} (i : thy-idx T)
  (σ : Subst (thy-ctx T i) (thy-cls T i) C) →
  -------------------------------------------
  Proof T {C = C} {Γ = thy-ctx T i} (Subst-Formula σ (thy-axi T i))
axiom-Subst {T = T} i σ = ≡-subst (λ Ξ → Proof T (Subst-Formula σ Ξ)) id-ren-Formula (axiom i σ id-ren)

axiom-exact : 
  ∀ {T} (i : thy-idx T) →
  -----------------------
  Proof T (thy-axi T i)
axiom-exact {T = T} i = ≡-subst (λ Ξ → Proof T Ξ) id-ren-Formula (axiom-ren i id-ren)

ren-Proof : ∀ {T C Γ Δ} {Φ : Formula C Γ} (r : ren Γ Δ) → Proof T Φ → Proof T (ren-Formula r Φ)
ren-Proof {T = T} r (axiom i σ r') =
  ≡-subst
    (λ Ξ → Proof T Ξ)
    (sym
      (trans
        (comp-rS-Formula {Φ = ren-Formula r' (thy-axi T i)} σ r)
        (cong (λ Ξ → Subst-Formula (comp-rS r σ) Ξ) (ren-comp-Formula r' r))))
    (axiom i (comp-rS r σ) (r ∘ r'))
ren-Proof r ⇔-refl = ⇔-refl
ren-Proof r (∧-cong p p') = ∧-cong (ren-Proof r p) (ren-Proof r p')
ren-Proof r (⇔-cong p p') = ⇔-cong (ren-Proof r p) (ren-Proof r p')
ren-Proof r (¬-cong p) = ¬-cong (ren-Proof r p)
ren-Proof r (all-cong p) = all-cong (ren-Proof (extend-ren r) p)
ren-Proof r (⇔-trans p p') = ⇔-trans (ren-Proof r p) (ren-Proof r p')
ren-Proof r (exists-cong p) = exists-cong (ren-Proof (extend-ren r) p)

Subst-Proof : ∀ {T C D Γ} {Φ : Formula C Γ} (σ : Subst Γ C D) → Proof T Φ → Proof T (Subst-Formula σ Φ)
Subst-Proof {T = T} σ (axiom i σ' r) =
  ≡-subst (λ Ξ → Proof T Ξ) (sym (Subst-comp-Formula σ' σ)) (axiom i (σ ∘c σ') r)
Subst-Proof σ ⇔-refl = ⇔-refl
Subst-Proof σ (∧-cong p p') = ∧-cong (Subst-Proof σ p) (Subst-Proof σ p')
Subst-Proof σ (⇔-cong p p') = ⇔-cong (Subst-Proof σ p) (Subst-Proof σ p')
Subst-Proof σ (¬-cong p) = ¬-cong (Subst-Proof σ p)
Subst-Proof σ (all-cong p) = all-cong (Subst-Proof (extend-Subst σ) p)
Subst-Proof σ (⇔-trans p p') = ⇔-trans (Subst-Proof σ p) (Subst-Proof σ p')
Subst-Proof σ (exists-cong p) = exists-cong (Subst-Proof (extend-Subst σ) p)

subst-dist-⇔ : ∀ {T C Γ} {Φ Ψ : Formula C (extend Γ)} (x : Var Γ) → Proof T (Φ ⇔ Ψ) → Proof T (Φ [ svar x ]F ⇔ Ψ [ svar x ]F)
subst-dist-⇔ x p = ren-Proof (ren₀ x) p -- all-elim (all-intro p) ; if we can cope with having all-elim

eq-to-⇔ : ∀ {Γ C T} {Φ Ψ : Formula Γ C} → Φ ≡ Ψ → Proof T (Φ ⇔ Ψ)
eq-to-⇔ refl = ⇔-refl

⇔-∈-subst : ∀ {Γ} {Φ : Formula₀ (extend Γ)} →
  Proof CT (svar zero ∈ (class (extend-Formula-ctx Φ)) ⇔ (extend-Formula-ctx Φ) [ svar zero ]F)
⇔-∈-subst {Γ} {Φ} = axiom-exact (set∈class 𝟘 (extend Γ) zero (extend-Formula-ctx Φ))