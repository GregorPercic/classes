open import Syntax
open import Substitutions
open import Theory


weaken : ∀ {Γ} → formula Γ → formula (extend Γ)
weaken = ren-formula suc

weaken-l : ∀ {Γ} → List (formula Γ) → List (formula (extend Γ))
weaken-l l = map weaken l

data proof (thy : theory) : {Γ : Ctx} → List (formula Γ) → formula Γ → Set where
  -- Non-structural rules

  axiom :
    ∀ {Γ} {hyp} (i : thy-idx thy)
    (r : ren (thy-ctx thy i) Γ) →
    proof thy hyp (ren-formula r (thy-axi thy i))

  -- source: https://www.enseignement.polytechnique.fr/informatique/MPRI/2-7-1/2024/notes.pdf ; p. 15

  hyp-ax : ∀ {Γ} {hyp} {φ : formula Γ} →
    hyp ∋ φ →
    -------------
    proof thy hyp φ

  lem : ∀ {Γ} {hyp} {φ : formula Γ} →
    ----------------------------------
    proof thy hyp (((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ)

  -- Introduction rules

  ≈-i : ∀ {Γ} {hyp} {t : term Γ} →
    -------------------
    proof thy hyp (t ≈ t)

  ∧-i : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy hyp φ →
    proof thy hyp ψ →
    --------------------
    proof thy hyp (φ ∧ ψ)

  ⇒-i : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy (hyp ∷ φ) ψ →
    --------------------
    proof thy hyp (φ ⇒ ψ)

  ⇔-i : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy hyp (φ ⇒ ψ) →
    proof thy hyp (ψ ⇒ φ) →
    ----------------------
    proof thy hyp (φ ⇔ ψ)

  all-i :
    ∀ {Γ} {hyp} {φ : formula (extend Γ)} →
    proof thy (weaken-l hyp) φ →
    ---------------
    proof thy hyp (all φ)

  exists-i :
    ∀ {Γ} {hyp} {φ : formula (extend Γ)} →
    (t : term Γ) →
    proof thy hyp (φ [ t ]f) →
    ------------------------
    proof thy hyp (exists φ)
  
  -- Elimination rules

  ⊥-e : ∀ {Γ} {hyp} {φ : formula Γ} →
    proof thy hyp ⊥ →
    ---------------
    proof thy hyp φ

  ∧-e-l : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy hyp (φ ∧ ψ) →
    ---------------------
    proof thy hyp φ

  ∧-e-r : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy hyp (φ ∧ ψ) →
    ---------------------
    proof thy hyp ψ

  ⇒-e : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy hyp (φ ⇒ ψ) →
    proof thy hyp φ →
    ---------------
    proof thy hyp ψ

  ⇔-e-lr : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy hyp (φ ⇔ ψ) →
    ----------------------
    proof thy hyp (φ ⇒ ψ)

  ⇔-e-rl : ∀ {Γ} {hyp} {φ ψ : formula Γ} →
    proof thy hyp (φ ⇔ ψ) →
    ----------------------
    proof thy hyp (ψ ⇒ φ)

  exists-e : ∀ {Γ} {hyp} {φ : formula (extend Γ)} {ψ : formula Γ} →
    proof thy hyp (exists φ) →
    proof thy (weaken-l hyp ∷ φ) (weaken ψ) →
    ---------------------------------------
    proof thy hyp ψ

  all-e : ∀ {Γ} {hyp} {φ : formula (extend Γ)} →
    (t : term Γ) →
    proof thy hyp (all φ) →
    ----------------------
    proof thy hyp (φ [ t ]f)
  
  -- source: https://link.springer.com/book/10.1007/978-1-4419-1221-3 ; p. 92

  ≈-e : ∀ {Γ} {hyp} {φ : formula (extend Γ)} {t u : term Γ} →
    proof thy hyp (t ≈ u) →
    proof thy hyp (φ [ t ]f) →
    ------------------------
    proof thy hyp (φ [ u ]f)

transport-proof : ∀ {thy Γ hyp} {φ ψ : formula Γ} → (φ ≡ ψ) → proof thy hyp φ → proof thy hyp ψ
transport-proof {thy = thy} {hyp = hyp} e p = ≡-subst (λ ξ → proof thy hyp ξ) e p

transport-proof-hyp : ∀ {thy Γ hyp hyp'} {φ : formula Γ} → (hyp ≡ hyp') → proof thy hyp φ → proof thy hyp' φ
transport-proof-hyp {thy = thy} e p = ≡-subst (λ h → proof thy h _) e p

⇔-refl : ∀ {thy Γ} {Hyp} {φ : formula Γ} → proof thy Hyp (φ ⇔ φ)
⇔-refl =
  ⇔-i
    (⇒-i (hyp-ax here))
    (⇒-i (hyp-ax here))

all-⇔-refl : ∀ {thy Γ} {Hyp} {φ : formula (extend Γ)} → proof thy Hyp (all (φ ⇔ φ))
all-⇔-refl = all-i ⇔-refl

eq-to-⇔ : ∀ {Γ thy hyp} {φ ψ : formula Γ} → φ ≡ ψ → proof thy hyp (φ ⇔ ψ)
eq-to-⇔ refl = ⇔-refl

conservation-equiv : ∀ {thy Γ hyp} {x : Var Γ} {φ : formula (extend Γ)} →
  -------------------------------------------------------------------
  proof thy hyp (φ [ svar x ]f ⇔ exists (svar zero ≈ svar (suc x) ∧ φ))
conservation-equiv {x = x} =
  ⇔-i
    (⇒-i (exists-i (svar x) (∧-i ≈-i (hyp-ax here))))
    (⇒-i
      (exists-e (hyp-ax here)
      (transport-proof
        lemma
        (≈-e (∧-e-l (hyp-ax here))
          (transport-proof
            (sym ren₀-zero-extend-ren-suc-inv-formula)
            (∧-e-r (hyp-ax here)))))))
  where
    lemma : ∀ {Γ} {x : Var Γ} {φ : formula (extend Γ)} →
      ren-formula (ren₀ (suc x)) (ren-formula (extend-ren suc) φ) ≡ ren-formula suc (ren-formula (ren₀ x) φ)
    lemma {φ = φ} =
      trans
        (ren-comp-formula _ _)
        (trans
          (cong (λ r → ren-formula r φ) lemma')
          (sym (ren-comp-formula _ _)))
      where
        lemma' : ∀ {Γ} {x : Var Γ} → ren₀ (suc x) ∘ extend-ren suc ≡ suc ∘ (ren₀ x)
        lemma' = fun-ext λ {zero → refl ; (suc x) → refl}