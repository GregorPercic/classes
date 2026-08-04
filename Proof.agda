open import Data.List hiding (all) renaming (_∷_ to _∷l_) public

open import Syntax
open import Substitutions
open import Theory

_∷_ : {X : Set} → List X → X → List X
_∷_ tl h = h ∷l tl

data _∋_ {X : Set} : List X → X → Set where
  here : ∀ {x xs} → (xs ∷ x) ∋ x
  there : ∀ {x y xs} → xs ∋ x → (xs ∷ y) ∋ x

weaken : ∀ {C Γ} → Formula C Γ → Formula C (extend Γ)
weaken = ren-Formula suc

weaken-l : ∀ {C Γ} → List (Formula C Γ) → List (Formula C (extend Γ))
weaken-l l = map weaken l

data Proof (T : Theory) {C : Set} : {Γ : Ctx} → List (Formula C Γ) → Formula C Γ → Set₂ where
  axiom :
    ∀ {Γ} {Hyp} (i : thy-idx T)
    (σ : Subst Γ (thy-cls T i) C)
    (r : ren (thy-ctx T i) Γ) →
    Proof T Hyp (Subst-Formula σ (ren-Formula r (thy-axi T i)))

  -- source: https://www.enseignement.polytechnique.fr/informatique/MPRI/2-7-1/2024/notes.pdf ; p. 15

  -- Non-structural rules

  Hyp-ax : ∀ {Γ} {Hyp} {Φ : Formula C Γ} →
    Hyp ∋ Φ →
    -------------
    Proof T Hyp Φ

  -- Introduction rules

  ≈-refl : ∀ {Γ} {Hyp} {t : Term C Γ} →
    -------------------
    Proof T Hyp (t ≈ t)

  ∧-i : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp Φ →
    Proof T Hyp Ψ →
    --------------------
    Proof T Hyp (Φ ∧ Ψ)

  ⇒-i : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T (Hyp ∷ Φ) Ψ →
    --------------------
    Proof T Hyp (Φ ⇒ Ψ)

  ⇔-i : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp (Φ ⇒ Ψ) →
    Proof T Hyp (Ψ ⇒ Φ) →
    ----------------------
    Proof T Hyp (Φ ⇔ Ψ)

  all-i :
    ∀ {Γ} {Hyp} {Φ : Formula C (extend Γ)} →
    Proof T (weaken-l Hyp) Φ →
    ---------------
    Proof T Hyp (all Φ)

  exists-i :
    ∀ {Γ} {Hyp} {Φ : Formula C (extend Γ)} →
    (t : term Γ) →
    Proof T Hyp (Φ [ t ]F) →
    ------------------------
    Proof T Hyp (exists Φ)
  
  -- Elimination rules

  ⊥-e : ∀ {Γ} {Hyp} {Φ : Formula C Γ} →
    Proof T Hyp ⊥ →
    ---------------
    Proof T Hyp Φ

  ∧-e-l : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp (Φ ∧ Ψ) →
    ---------------------
    Proof T Hyp Φ

  ∧-e-r : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp (Φ ∧ Ψ) →
    ---------------------
    Proof T Hyp Ψ

  ⇒-e : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp (Φ ⇒ Ψ) →
    Proof T Hyp Φ →
    ---------------
    Proof T Hyp Ψ

  ⇔-e-lr : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp (Φ ⇔ Ψ) →
    ----------------------
    Proof T Hyp (Φ ⇒ Ψ)

  ⇔-e-rl : ∀ {Γ} {Hyp} {Φ Ψ : Formula C Γ} →
    Proof T Hyp (Φ ⇔ Ψ) →
    ----------------------
    Proof T Hyp (Ψ ⇒ Φ)

  exists-e : ∀ {Γ} {Hyp} {Φ : Formula C (extend Γ)} {Ψ : Formula C Γ} →
    Proof T Hyp (exists Φ) →
    Proof T (weaken-l Hyp ∷ Φ) (weaken Ψ) →
    ---------------------------------------
    Proof T Hyp Ψ

  all-e : ∀ {Γ} {Hyp} {Φ : Formula C (extend Γ)} →
    (t : term Γ) →
    Proof T Hyp (all Φ) →
    ----------------------
    Proof T Hyp (Φ [ t ]F)
  
  -- source: https://link.springer.com/book/10.1007/978-1-4419-1221-3 ; p. 92

  ≈-e : ∀ {Γ Hyp} {Φ : Formula C (extend Γ)} {t u : term Γ} →
    Proof T Hyp (inj-term t ≈ inj-term u) →
    Proof T Hyp (Φ [ t ]F) →
    ------------------------
    Proof T Hyp (Φ [ u ]F)

transport-proof : ∀ {T C Γ Hyp} {Φ Ψ : Formula C Γ} → (Φ ≡ Ψ) → Proof T Hyp Φ → Proof T Hyp Ψ
transport-proof {T = T} {Hyp = Hyp} e p = ≡-subst (λ Ξ → Proof T Hyp Ξ) e p

transport-proof-Hyp : ∀ {T C Γ Hyp Hyp'} {Φ : Formula C Γ} → (Hyp ≡ Hyp') → Proof T Hyp Φ → Proof T Hyp' Φ
transport-proof-Hyp {T = T} e p = ≡-subst (λ H → Proof T H _) e p

data _⊆-Hyp_ {C : Set} {Γ : Ctx} : List (Formula C Γ) → List (Formula C Γ) → Set where
  self : ∀ {Hyp} → Hyp ⊆-Hyp Hyp
  step : ∀ {Φ Hyp Hyp'} → Hyp ⊆-Hyp Hyp' → Hyp ⊆-Hyp (Hyp' ∷ Φ)
  both-step : ∀ {Φ Hyp Hyp'} → Hyp ⊆-Hyp Hyp' → (Hyp ∷ Φ) ⊆-Hyp (Hyp' ∷ Φ)

⊆-Hyp-lemma : ∀ {C Γ} {Φ : Formula C Γ} {Hyp Hyp'} → Hyp ⊆-Hyp Hyp' → Hyp ∋ Φ → Hyp' ∋ Φ
⊆-Hyp-lemma self is-in = is-in
⊆-Hyp-lemma (step sub) is-in = there (⊆-Hyp-lemma sub is-in)
⊆-Hyp-lemma (both-step sub) here = here
⊆-Hyp-lemma (both-step sub) (there is-in) = there (⊆-Hyp-lemma sub is-in)

-- Weakening as an admissible rule

weaken-l-preserves-⊆-Hyp : ∀ {C Γ} {Hyp Hyp' : List (Formula C Γ)} → Hyp ⊆-Hyp Hyp' → (weaken-l Hyp) ⊆-Hyp (weaken-l Hyp')
weaken-l-preserves-⊆-Hyp self = self
weaken-l-preserves-⊆-Hyp (step sub) = step (weaken-l-preserves-⊆-Hyp sub)
weaken-l-preserves-⊆-Hyp (both-step sub) = both-step (weaken-l-preserves-⊆-Hyp sub)

general-wk :
  ∀ {T C Γ} {Hyp Hyp'} {Φ : Formula C Γ}
  → Hyp ⊆-Hyp Hyp'
  → Proof T Hyp Φ
  -----------------
  → Proof T Hyp' Φ
general-wk sub (axiom i σ r) = axiom i σ r
general-wk sub (⊥-e p) = ⊥-e (general-wk sub p)
general-wk sub (Hyp-ax is-in) = Hyp-ax (⊆-Hyp-lemma sub is-in)
general-wk sub ≈-refl = ≈-refl
general-wk sub (∧-i p p') = ∧-i (general-wk sub p) (general-wk sub p')
general-wk sub (⇒-i p) = ⇒-i (general-wk (both-step sub) p)
general-wk sub (⇔-i p p') = ⇔-i (general-wk sub p) (general-wk sub p')
general-wk sub (all-i p) = all-i (general-wk (weaken-l-preserves-⊆-Hyp sub) p)
general-wk sub (exists-i t p) = exists-i t (general-wk sub p)
general-wk sub (∧-e-l p) = ∧-e-l (general-wk sub p)
general-wk sub (∧-e-r p) = ∧-e-r (general-wk sub p)
general-wk sub (⇒-e p p') = ⇒-e (general-wk sub p) (general-wk sub p')
general-wk sub (⇔-e-lr p) = ⇔-e-lr (general-wk sub p)
general-wk sub (⇔-e-rl p) = ⇔-e-rl (general-wk sub p)
general-wk sub (exists-e p p') = exists-e (general-wk sub p) (general-wk (both-step (weaken-l-preserves-⊆-Hyp sub)) p')
general-wk sub (all-e t p) = all-e t (general-wk sub p)
general-wk sub (≈-e eq p) = ≈-e (general-wk sub eq) (general-wk sub p)

wk :
  ∀ {T C Γ} {Hyp} {Φ Ψ : Formula C Γ}
  → Proof T Hyp Φ
  ---------------------
  → Proof T (Hyp ∷ Ψ) Φ
wk = general-wk (step self)

-- Derived rules of inference we need

⇔-refl : ∀ {T C Γ} {Hyp} {Φ : Formula C Γ} → Proof T Hyp (Φ ⇔ Φ)
⇔-refl =
  ⇔-i
    (⇒-i (Hyp-ax here))
    (⇒-i (Hyp-ax here))

∧-cong : ∀ {T C Γ} {Hyp} {Φ Φ' Ψ Ψ' : Formula C Γ} →
  Proof T Hyp (Φ ⇔ Φ') →
  Proof T Hyp (Ψ ⇔ Ψ') →
  -----------------------------
  Proof T Hyp (Φ ∧ Ψ ⇔ Φ' ∧ Ψ')
∧-cong p p' =
  ⇔-i
    (⇒-i
      (∧-i
        (⇒-e (⇔-e-lr (wk p)) (∧-e-l (Hyp-ax here)))
        (⇒-e (⇔-e-lr (wk p')) (∧-e-r (Hyp-ax here)))))
    (⇒-i
      (∧-i
        (⇒-e (⇔-e-rl (wk p)) (∧-e-l (Hyp-ax here)))
        (⇒-e (⇔-e-rl (wk p')) (∧-e-r (Hyp-ax here)))))

⇒-trans : ∀ {T C Γ} {Hyp} {Φ Φ' Φ'' : Formula C Γ} →
  Proof T Hyp (Φ ⇒ Φ') →
  Proof T Hyp (Φ' ⇒ Φ'') →
  ---------------------
  Proof T Hyp (Φ ⇒ Φ'')
⇒-trans p p' =
  ⇒-i
    (⇒-e
      (wk p')
      (⇒-e (wk p) (Hyp-ax here)))

⇔-sym : ∀ {T C Γ} {Hyp} {Φ Φ' : Formula C Γ} →
  Proof T Hyp (Φ ⇔ Φ') →
  ---------------------
  Proof T Hyp (Φ' ⇔ Φ)
⇔-sym p = ⇔-i (⇔-e-rl p) (⇔-e-lr p)

⇔-trans : ∀ {T C Γ} {Hyp} {Φ Φ' Φ'' : Formula C Γ} →
  Proof T Hyp (Φ ⇔ Φ') →
  Proof T Hyp (Φ' ⇔ Φ'') →
  ---------------------
  Proof T Hyp (Φ ⇔ Φ'')
⇔-trans p p' =
  ⇔-i
    (⇒-trans (⇔-e-lr p) (⇔-e-lr p'))
    (⇒-trans (⇔-e-rl p') (⇔-e-rl p))

⇒-cong : ∀ {T C Γ} {Hyp} {Φ Φ' Ψ Ψ' : Formula C Γ} →
  Proof T Hyp (Φ ⇔ Φ') →
  Proof T Hyp (Ψ ⇔ Ψ') →
  ----------------------------------
  Proof T Hyp ((Φ ⇒ Ψ) ⇔ (Φ' ⇒ Ψ'))
⇒-cong p p' =
  ⇔-i
    (⇒-i
      (⇒-trans
        (wk (⇔-e-rl p))
        (⇒-trans (Hyp-ax here) (wk (⇔-e-lr p')))))
    (⇒-i
      (⇒-trans
        (wk (⇔-e-lr p))
        (⇒-trans (Hyp-ax here) (wk (⇔-e-rl p')))))

⇔-cong : ∀ {T C Γ} {Hyp} {Φ Φ' Ψ Ψ' : Formula C Γ} →
  Proof T Hyp (Φ ⇔ Φ') →
  Proof T Hyp (Ψ ⇔ Ψ') →
  ----------------------------------
  Proof T Hyp ((Φ ⇔ Ψ) ⇔ (Φ' ⇔ Ψ'))
⇔-cong p p' =
  ⇔-i
    (⇒-i
      (⇔-trans
        (⇔-trans (wk (⇔-sym p)) (Hyp-ax here))
        (wk p')))
    (⇒-i
      (⇔-trans
        (⇔-trans (wk p) (Hyp-ax here))
        (wk (⇔-sym p'))))

all-lemma : ∀ {T C Γ} {Hyp} {Φ : Formula C (extend Γ)} →
  Proof T Hyp (weaken (all Φ)) →
  ------------------------------
  Proof T Hyp Φ
all-lemma p =
  transport-proof
    ren-zero-extend-ctx-id-Formula
    (all-e (svar zero) p)

all-cong : ∀ {T C Γ} {Hyp} {Φ Φ' : Formula C (extend Γ)} →
  Proof T (weaken-l Hyp) (Φ ⇔ Φ') →
  ----------------------------------
  Proof T Hyp (all Φ ⇔ all Φ')
all-cong p =
    ⇔-i
      (⇒-i
        (all-i
          (⇒-e
            (wk (⇔-e-lr p))
            (all-lemma (Hyp-ax here)))))
      (⇒-i
        (all-i
          (⇒-e
            (wk (⇔-e-rl p))
            (all-lemma (Hyp-ax here)))))

exists-lemma : ∀ {T C Γ} {Hyp} {Φ : Formula C (extend Γ)} →
  Proof T Hyp Φ →
  -------------------------------
  Proof T Hyp (weaken (exists Φ))
exists-lemma p =
  exists-i
    (svar zero)
    (transport-proof (sym ren-zero-extend-ctx-id-Formula) p)

exists-cong : ∀ {T C Γ} {Hyp} {Φ Φ' : Formula C (extend Γ)} →
  Proof T (weaken-l Hyp) (Φ ⇔ Φ') →
  -----------------------------------
  Proof T Hyp (exists Φ ⇔ exists Φ')
exists-cong {Φ = Φ} p =
  ⇔-i
    (⇒-i
      (exists-e
        (Hyp-ax here)
        (exists-lemma (⇒-e (wk (wk (⇔-e-lr p))) (Hyp-ax here)))))
    (⇒-i
      (exists-e
        (Hyp-ax here)
        (exists-lemma (⇒-e (wk (wk (⇔-e-rl p))) (Hyp-ax here)))))

conservation-equiv : ∀ {T C Γ Hyp} {x : Var Γ} {Φ : Formula C (extend Γ)} →
  -------------------------------------------------------------------
  Proof T Hyp (Φ [ svar x ]F ⇔ exists (svar zero ≈ svar (suc x) ∧ Φ))
conservation-equiv {x = x} =
  ⇔-i
    (⇒-i (exists-i (svar x) (∧-i ≈-refl (Hyp-ax here))))
    (⇒-i
      (exists-e (Hyp-ax here)
      (transport-proof
        suc-var-extend-suc-is-suc-ren-var
        (≈-e (∧-e-l (Hyp-ax here))
          (transport-proof
            (sym ren-zero-extend-ctx-id-Formula)
            (∧-e-r (Hyp-ax here)))))))

axiom-ren :
  ∀ {T Γ} (i : thy-idx T) {Hyp}
  (r : ren (thy-ctx T i) Γ) →
  -------------------------------------------------------------------
  Proof T {C = thy-cls T i} {Γ = Γ} Hyp (ren-Formula r (thy-axi T i))
axiom-ren {T = T} i {Hyp = Hyp} r = ≡-subst (λ Ξ → Proof T Hyp Ξ) (id-Subst-Formula) (axiom i id-Subst r)

axiom-Subst :
  ∀ {T C} (i : thy-idx T) {Hyp}
  (σ : Subst (thy-ctx T i) (thy-cls T i) C) →
  ---------------------------------------------------------------------
  Proof T {C = C} {Γ = thy-ctx T i} Hyp (Subst-Formula σ (thy-axi T i))
axiom-Subst {T = T} i {Hyp = Hyp} σ = ≡-subst (λ Ξ → Proof T Hyp (Subst-Formula σ Ξ)) id-ren-Formula (axiom i σ id-ren)

axiom-exact :
  ∀ {T} (i : thy-idx T) {Hyp} →
  -----------------------
  Proof T Hyp (thy-axi T i)
axiom-exact {T = T} i {Hyp = Hyp} = ≡-subst (λ Ξ → Proof T Hyp Ξ) id-ren-Formula (axiom-ren i id-ren)

ren-list-mem : ∀ {C Γ Δ Hyp} {Φ : Formula C Γ} (r : ren Γ Δ) → Hyp ∋ Φ → (map (ren-Formula r) Hyp) ∋ (ren-Formula r Φ)
ren-list-mem {Φ = Φ} r here = here
ren-list-mem {Φ = Φ} r (there is-in) = there (ren-list-mem r is-in)

Hyp-weaken-l-lemma : ∀ {Γ Δ C} {Hyp : List (Formula C Γ)} (r : ren Γ Δ) →
  weaken-l (map (ren-Formula r) Hyp) ≡ map (ren-Formula (extend-ren r)) (weaken-l Hyp)
Hyp-weaken-l-lemma {Hyp = []} r = refl
Hyp-weaken-l-lemma {Hyp = Φ ∷l Hyp} r = cong₂ _∷l_ (sym (renaming-suc-commute-Formula r)) (Hyp-weaken-l-lemma r)

ren-Proof : ∀ {T C Γ Δ Hyp} {Φ : Formula C Γ} (r : ren Γ Δ) → Proof T Hyp Φ → Proof T (map (ren-Formula r) Hyp) (ren-Formula r Φ)
ren-Proof {T = T} {Hyp = Hyp} r (axiom i σ r') =
  transport-proof
    (sym
      (trans
        (comp-rS-Formula {Φ = ren-Formula r' (thy-axi T i)} σ r)
        (cong (λ Ξ → Subst-Formula (comp-rS r σ) Ξ) (ren-comp-Formula r' r))))
    (axiom i (comp-rS r σ) (r ∘ r'))
ren-Proof r (⊥-e p) = ⊥-e (ren-Proof r p)
ren-Proof r (Hyp-ax is-in) = Hyp-ax (ren-list-mem r is-in)
ren-Proof r ≈-refl = ≈-refl
ren-Proof r (∧-i p p') = ∧-i (ren-Proof r p) (ren-Proof r p')
ren-Proof r (⇒-i p) = ⇒-i (ren-Proof r p)
ren-Proof r (⇔-i p p') = ⇔-i (ren-Proof r p) (ren-Proof r p')
ren-Proof r (all-i p) = all-i (transport-proof-Hyp (sym (Hyp-weaken-l-lemma r)) (ren-Proof (extend-ren r) p))
ren-Proof r (exists-i t p) = exists-i (ren-term r t) (transport-proof (sym (ren-term-subst-lemma {t = t} r)) (ren-Proof r p))
ren-Proof r (∧-e-l p) = ∧-e-l (ren-Proof r p)
ren-Proof r (∧-e-r p) = ∧-e-r (ren-Proof r p)
ren-Proof r (⇒-e p p') = ⇒-e (ren-Proof r p) (ren-Proof r p')
ren-Proof r (⇔-e-lr p) = ⇔-e-lr (ren-Proof r p)
ren-Proof r (⇔-e-rl p) = ⇔-e-rl (ren-Proof r p)
ren-Proof r (exists-e p p') =
  exists-e
    (ren-Proof r p)
    (transport-proof-Hyp
      (cong₂ _∷_ (sym (Hyp-weaken-l-lemma r)) refl)
      (transport-proof
        (renaming-suc-commute-Formula r)
        (ren-Proof (extend-ren r) p')))
ren-Proof r (all-e t p) = transport-proof (ren-term-subst-lemma {t = t} r) (all-e (ren-term r t) (ren-Proof r p))
ren-Proof r (≈-e {Φ = Φ} {t = t} {u = u} eq p) =
  transport-proof
    (ren-term-subst-lemma {t = u} {Φ = Φ} r)
    (≈-e
      (transport-proof
        (cong₂ _≈_ (inj-term-ren-commute r) (inj-term-ren-commute r))
        (ren-Proof r eq))
        (transport-proof
          (sym (ren-term-subst-lemma {t = t} r))
          (ren-Proof r p))) 

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

subst-dist-⇔ : ∀ {T C Γ Hyp} {Φ Ψ : Formula C (extend Γ)} (x : Var Γ) → Proof T (weaken-l Hyp) (Φ ⇔ Ψ) → Proof T Hyp (Φ [ svar x ]F ⇔ Ψ [ svar x ]F)
subst-dist-⇔ x p = all-e (svar x) (all-i p) -- ren-Proof (ren₀ x) p

eq-to-⇔ : ∀ {Γ C T Hyp} {Φ Ψ : Formula Γ C} → Φ ≡ Ψ → Proof T Hyp (Φ ⇔ Ψ)
eq-to-⇔ refl = ⇔-refl

⇔-∈-subst : ∀ {Γ} {Hyp} {Φ : Formula₀ (extend Γ)} →
  Proof CT Hyp (svar zero ∈ (class (extend-Formula-ctx Φ)) ⇔ (extend-Formula-ctx Φ) [ svar zero ]F)
⇔-∈-subst {Γ = Γ} {Φ = Φ} = axiom-exact (set∈class 𝟘 (extend Γ) zero (extend-Formula-ctx Φ))
