open import Syntax
open import Substitutions
open import TTheory

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

transport-Proof : ∀ {T C Γ Hyp} {Φ Ψ : Formula C Γ} → (Φ ≡ Ψ) → Proof T Hyp Φ → Proof T Hyp Ψ
transport-Proof {T = T} {Hyp = Hyp} e p = ≡-subst (λ Ξ → Proof T Hyp Ξ) e p

transport-Proof-Hyp : ∀ {T C Γ Hyp Hyp'} {Φ : Formula C Γ} → (Hyp ≡ Hyp') → Proof T Hyp Φ → Proof T Hyp' Φ
transport-Proof-Hyp {T = T} e p = ≡-subst (λ H → Proof T H _) e p


-- Weakening as an admissible rule
-- the subset premise was suggested by ChatGPT, but all code is my original work

ren-list-mem : ∀ {C Γ Δ Hyp} {Φ : Formula C Γ} (r : ren Γ Δ) → Hyp ∋ Φ → (map (ren-Formula r) Hyp) ∋ (ren-Formula r Φ)
ren-list-mem {Φ = Φ} r here = here
ren-list-mem {Φ = Φ} r (there is-in) = there (ren-list-mem r is-in)

_⊆-Hyp_ : {C : Set} {Γ : Ctx} → List (Formula C Γ) → List (Formula C Γ) → Set
Hyp ⊆-Hyp Hyp' = ∀ {Φ} → Hyp ∋ Φ → Hyp' ∋ Φ

⊆-Hyp-both-step : ∀ {C Γ Hyp Hyp'} {Φ : Formula C Γ} → Hyp ⊆-Hyp Hyp' → (Hyp ∷ Φ) ⊆-Hyp (Hyp' ∷ Φ)
⊆-Hyp-both-step sub here = here
⊆-Hyp-both-step sub (there is-in) = there (sub is-in)

⊆-Hyp-weaken-l : ∀ {C Γ} {Hyp Hyp' : List (Formula C Γ)} → Hyp ⊆-Hyp Hyp' → weaken-l Hyp ⊆-Hyp weaken-l Hyp'
⊆-Hyp-weaken-l {Hyp = []} sub ()
⊆-Hyp-weaken-l {Hyp = Φ ∷l Hyp} sub here = ren-list-mem suc (sub here)
⊆-Hyp-weaken-l {Hyp = Φ ∷l Hyp} sub (there is-in) = ⊆-Hyp-weaken-l (λ is-in' → sub (there is-in')) is-in

general-wk :
  ∀ {T C Γ} {Hyp Hyp'} {Φ : Formula C Γ}
  → Hyp ⊆-Hyp Hyp'
  → Proof T Hyp Φ
  -----------------
  → Proof T Hyp' Φ
general-wk sub (axiom i σ r) = axiom i σ r
general-wk sub (Hyp-ax is-in) = Hyp-ax (sub is-in)
general-wk sub ≈-refl = ≈-refl
general-wk sub (∧-i p p') = ∧-i (general-wk sub p) (general-wk sub p')
general-wk sub (⇒-i p) = ⇒-i (general-wk (⊆-Hyp-both-step sub) p)
general-wk sub (⇔-i p p') = ⇔-i (general-wk sub p) (general-wk sub p')
general-wk sub (all-i p) = all-i (general-wk (⊆-Hyp-weaken-l sub) p)
general-wk sub (exists-i t p) = exists-i t (general-wk sub p)
general-wk sub (⊥-e p) = ⊥-e (general-wk sub p)
general-wk sub (∧-e-l p) = ∧-e-l (general-wk sub p)
general-wk sub (∧-e-r p) = ∧-e-r (general-wk sub p)
general-wk sub (⇒-e p p') = ⇒-e (general-wk sub p) (general-wk sub p')
general-wk sub (⇔-e-lr p) = ⇔-e-lr (general-wk sub p)
general-wk sub (⇔-e-rl p) = ⇔-e-rl (general-wk sub p)
general-wk sub (exists-e p p') = exists-e (general-wk sub p) (general-wk (⊆-Hyp-both-step (⊆-Hyp-weaken-l sub)) p')
general-wk sub (all-e t p) = all-e t (general-wk sub p)
general-wk sub (≈-e p p') = ≈-e (general-wk sub p) (general-wk sub p')

wk :
  ∀ {T C Γ} {Hyp} {Φ Ψ : Formula C Γ}
  → Proof T Hyp Φ
  ---------------------
  → Proof T (Hyp ∷ Ψ) Φ
wk = general-wk (λ is-in → there is-in)

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
  transport-Proof
    ren₀-zero-extend-ren-suc-inv-Formula
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
    (transport-Proof (sym ren₀-zero-extend-ren-suc-inv-Formula) p)

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
      (transport-Proof
        lemma
        (≈-e (∧-e-l (Hyp-ax here))
          (transport-Proof
            (sym ren₀-zero-extend-ren-suc-inv-Formula)
            (∧-e-r (Hyp-ax here)))))))
  where
    lemma : ∀ {C Γ} {x : Var Γ} {Φ : Formula C (extend Γ)} →
      ren-Formula (ren₀ (suc x)) (ren-Formula (extend-ren suc) Φ) ≡ ren-Formula suc (ren-Formula (ren₀ x) Φ)
    lemma {Φ = Φ} =
      trans
        (ren-comp-Formula _ _)
        (trans
          (cong (λ r → ren-Formula r Φ) lemma')
          (sym (ren-comp-Formula _ _)))
      where
        lemma' : ∀ {Γ} {x : Var Γ} → ren₀ (suc x) ∘ extend-ren suc ≡ suc ∘ (ren₀ x)
        lemma' = fun-ext λ {zero → refl ; (suc x) → refl}

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

Hyp-weaken-l-lemma-ren : ∀ {Γ Δ C} {Hyp : List (Formula C Γ)} (r : ren Γ Δ) →
  weaken-l (map (ren-Formula r) Hyp) ≡ map (ren-Formula (extend-ren r)) (weaken-l Hyp)
Hyp-weaken-l-lemma-ren {Hyp = []} r = refl
Hyp-weaken-l-lemma-ren {Hyp = Φ ∷l Hyp} r = cong₂ _∷l_ (sym (extend-ren-r-suc-lemma-Formula r)) (Hyp-weaken-l-lemma-ren r)

ren-Proof : ∀ {T C Γ Δ Hyp} {Φ : Formula C Γ} (r : ren Γ Δ) → Proof T Hyp Φ → Proof T (map (ren-Formula r) Hyp) (ren-Formula r Φ)
ren-Proof {T = T} {Hyp = Hyp} r (axiom i σ r') =
  transport-Proof
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
ren-Proof r (all-i p) = all-i (transport-Proof-Hyp (sym (Hyp-weaken-l-lemma-ren r)) (ren-Proof (extend-ren r) p))
ren-Proof r (exists-i t p) = exists-i (ren-term r t) (transport-Proof (sym (ren-term-subst-lemma {t = t} r)) (ren-Proof r p))
ren-Proof r (∧-e-l p) = ∧-e-l (ren-Proof r p)
ren-Proof r (∧-e-r p) = ∧-e-r (ren-Proof r p)
ren-Proof r (⇒-e p p') = ⇒-e (ren-Proof r p) (ren-Proof r p')
ren-Proof r (⇔-e-lr p) = ⇔-e-lr (ren-Proof r p)
ren-Proof r (⇔-e-rl p) = ⇔-e-rl (ren-Proof r p)
ren-Proof r (exists-e p p') =
  exists-e
    (ren-Proof r p)
    (transport-Proof-Hyp
      (cong₂ _∷_ (sym (Hyp-weaken-l-lemma-ren r)) refl)
      (transport-Proof
        (extend-ren-r-suc-lemma-Formula r)
        (ren-Proof (extend-ren r) p')))
ren-Proof r (all-e t p) = transport-Proof (ren-term-subst-lemma {t = t} r) (all-e (ren-term r t) (ren-Proof r p))
ren-Proof r (≈-e {Φ = Φ} {t = t} {u = u} eq p) =
  transport-Proof
    (ren-term-subst-lemma {t = u} {Φ = Φ} r)
    (≈-e
      (transport-Proof
        (cong₂ _≈_ (ren-inj-term r) (ren-inj-term r))
        (ren-Proof r eq))
      (transport-Proof
        (sym (ren-term-subst-lemma {t = t} r))
        (ren-Proof r p))) 

Subst-list-mem : ∀ {C D Γ Hyp} {Φ : Formula C Γ} (σ : Subst Γ C D) → Hyp ∋ Φ → map (Subst-Formula σ) Hyp ∋ Subst-Formula σ Φ
Subst-list-mem σ here = here
Subst-list-mem σ (there is-in) = there (Subst-list-mem σ is-in)

Hyp-weaken-l-lemma-Subst : ∀ {C D Γ Hyp} (σ : Subst Γ C D) → map (Subst-Formula (extend-Subst σ)) (weaken-l Hyp) ≡ weaken-l (map (Subst-Formula σ) Hyp)
Hyp-weaken-l-lemma-Subst {Hyp = []} σ = refl
Hyp-weaken-l-lemma-Subst {Hyp = Φ ∷l Hyp} σ = cong₂ _∷l_ (extend-Subst-suc-lemma σ) (Hyp-weaken-l-lemma-Subst σ)

Subst-Proof : ∀ {T C D Γ Hyp} {Φ : Formula C Γ} (σ : Subst Γ C D) → Proof T Hyp Φ → Proof T (map (Subst-Formula σ) Hyp) (Subst-Formula σ Φ)
Subst-Proof σ (axiom i σ' r) = transport-Proof (sym (Subst-comp-Formula σ' σ)) (axiom i (σ ∘c σ') r)
Subst-Proof σ (Hyp-ax is-in) = Hyp-ax (Subst-list-mem σ is-in)
Subst-Proof σ ≈-refl = ≈-refl
Subst-Proof σ (∧-i p p') = ∧-i (Subst-Proof σ p) (Subst-Proof σ p')
Subst-Proof σ (⇒-i p) = ⇒-i (Subst-Proof σ p)
Subst-Proof σ (⇔-i p p') = ⇔-i (Subst-Proof σ p) (Subst-Proof σ p')
Subst-Proof σ (all-i p) = all-i (transport-Proof-Hyp (Hyp-weaken-l-lemma-Subst σ) (Subst-Proof (extend-Subst σ) p))
Subst-Proof σ (exists-i t p) = exists-i t (transport-Proof (sym (subst-term-extend-Subst-Formula {t = t} σ)) (Subst-Proof σ p))
Subst-Proof σ (⊥-e p) = ⊥-e (Subst-Proof σ p)
Subst-Proof σ (∧-e-l p) = ∧-e-l (Subst-Proof σ p)
Subst-Proof σ (∧-e-r p) = ∧-e-r (Subst-Proof σ p)
Subst-Proof σ (⇒-e p p') = ⇒-e (Subst-Proof σ p) (Subst-Proof σ p')
Subst-Proof σ (⇔-e-lr p) = ⇔-e-lr (Subst-Proof σ p)
Subst-Proof σ (⇔-e-rl p) = ⇔-e-rl (Subst-Proof σ p)
Subst-Proof σ (exists-e p p') =
  exists-e
    (Subst-Proof σ p)
    (transport-Proof-Hyp
      (cong₂ _∷_ (Hyp-weaken-l-lemma-Subst σ) refl)
      (transport-Proof
        (extend-Subst-suc-lemma σ)
        (Subst-Proof (extend-Subst σ) p')))
Subst-Proof σ (all-e t p) = transport-Proof (subst-term-extend-Subst-Formula {t = t} σ) (all-e t (Subst-Proof σ p))
Subst-Proof σ (≈-e {Φ = Φ} {t = t} {u = u} eq p) =
  transport-Proof
    (subst-term-extend-Subst-Formula {t = u} {Φ = Φ} σ)
    (≈-e
      (transport-Proof
        (cong₂ _≈_ (Subst-inj-term-eq {t = t} σ) (Subst-inj-term-eq {t = u} σ))
        (Subst-Proof σ eq))
      (transport-Proof
        (sym (subst-term-extend-Subst-Formula {t = t} σ))
        (Subst-Proof σ p)))

subst-dist-⇔ : ∀ {T C Γ Hyp} {Φ Ψ : Formula C (extend Γ)} (x : Var Γ) → Proof T (weaken-l Hyp) (Φ ⇔ Ψ) → Proof T Hyp (Φ [ svar x ]F ⇔ Ψ [ svar x ]F)
subst-dist-⇔ x p = all-e (svar x) (all-i p) -- ren-Proof (ren₀ x) p

eq-to-⇔ : ∀ {Γ C T Hyp} {Φ Ψ : Formula Γ C} → Φ ≡ Ψ → Proof T Hyp (Φ ⇔ Ψ)
eq-to-⇔ refl = ⇔-refl

⇔-∈-subst : ∀ {Γ} {Hyp} {Φ : Formula₀ (extend Γ)} →
  Proof CT Hyp (svar zero ∈ (class (extend-ren-suc-Formula Φ)) ⇔ (extend-ren-suc-Formula Φ) [ svar zero ]F)
⇔-∈-subst {Γ = Γ} {Φ = Φ} = axiom-exact (set∈class 𝟘 (extend Γ) zero (extend-ren-suc-Formula Φ))
