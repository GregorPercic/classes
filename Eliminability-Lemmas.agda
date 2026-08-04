open import Syntax
open import Substitutions


elim : ∀ {Γ} → Formula₀ Γ → formula Γ
elim ⊥ = ⊥
elim (svar x ≈ svar y) = svar x ≈ svar y
elim (svar x ≈ class Φ) = all (svar zero ∈ svar (suc x) ⇔ elim Φ)
elim (class Φ ≈ svar x) = all (elim Φ ⇔ svar zero ∈ svar (suc x))
elim (class Φ ≈ class Ψ) = all (elim Φ ⇔ elim Ψ)
elim (svar x ∈ svar y) = svar x ∈ svar y
elim (svar x ∈ class Φ) = (elim Φ) [ svar x ]f
elim (class Φ ∈ svar x) = exists ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-ctx (elim Φ))) ∧ svar zero ∈ svar (suc x))
elim (class Φ ∈ class Ψ) = exists ((all (svar zero ∈ svar (suc zero) ⇔ extend-formula-ctx (elim Φ))) ∧ elim Ψ)
elim (Φ ∧ Ψ) = elim Φ ∧ elim Ψ
elim (Φ ⇔ Ψ) = elim Φ ⇔ elim Ψ
elim (Φ ⇒ Ψ) = elim Φ ⇒ elim Ψ
elim (all Φ) = all (elim Φ)
elim (exists Φ) = exists (elim Φ)

eq-subst-zero-Formula : ∀ {C Γ} {Φ : Formula C (extend Γ)} → (extend-Formula-ctx Φ) [ svar zero ]F ≡ Φ
eq-subst-zero-Formula {Φ = Φ} =
  trans
    (trans
      (ren-comp-Formula (extend-ren suc) (ren₀ zero))
      (cong
        (λ f → ren-Formula f Φ)
        ren-zero-extend-ctx-id))
    id-ren-Formula

elim-renamings-commute : ∀ {Γ Δ} {Φ : Formula₀ Γ} (r : ren Γ Δ) →
  elim (ren-Formula r Φ) ≡ ren-formula r (elim Φ)
elim-renamings-commute {Φ = ⊥} r = refl
elim-renamings-commute {Φ = svar x ≈ svar y} r = refl
elim-renamings-commute {Φ = svar x ≈ class Φ} r =
  cong (λ Ξ → all (svar zero ∈ svar (suc (r x)) ⇔ Ξ)) (elim-renamings-commute {Φ = Φ} (extend-ren r))
elim-renamings-commute {Φ = class Φ ≈ svar x} r =
  cong (λ Ξ → all (Ξ ⇔ svar zero ∈ svar (suc (r x)))) (elim-renamings-commute {Φ = Φ} (extend-ren r))
elim-renamings-commute {Φ = class Φ ≈ class Ψ} r =
  cong₂
    (λ Ξ Ξ' → all (Ξ ⇔ Ξ'))
    (elim-renamings-commute {Φ = Φ} (extend-ren r))
    (elim-renamings-commute {Φ = Ψ} (extend-ren r))
elim-renamings-commute {Φ = svar x ∈ svar y} r = refl
elim-renamings-commute {Φ = svar x ∈ class Φ} r =
  trans
    (trans
      (trans
        (cong
          (λ Ξ → ren-formula (ren₀ (r x)) Ξ)
          (elim-renamings-commute {Φ = Φ} (extend-ren r)))
        (ren-comp-formula (extend-ren r) (ren₀ (r x))))
      (cong (λ r' → ren-formula r' (elim Φ)) (lemma r)))
    (sym (ren-comp-formula (ren₀ x) r))
  where
    lemma : ∀ {Γ Δ} {x : Var Γ} (r : ren Γ Δ) → ren₀ (r x) ∘ (extend-ren r) ≡ r ∘ (ren₀ x)
    lemma r = fun-ext λ {zero → refl ; (suc x) → refl}
elim-renamings-commute {Φ = class Φ ∈ svar x} r =
  cong (λ Ξ → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ svar zero ∈ svar (suc (r x)))) lemma
  where
    lemma :
      extend-formula-ctx (elim (ren-Formula (extend-ren r) Φ))
        ≡
      ren-formula (extend-ren (extend-ren r)) (extend-formula-ctx (elim Φ))
    lemma =
      trans
        (trans
          (trans
            (cong (λ φ → extend-formula-ctx φ) (elim-renamings-commute {Φ = Φ} (extend-ren r)))
            (ren-comp-formula (extend-ren r) (extend-ren suc)))
          (cong (λ r' → ren-formula r' (elim Φ)) (extend-suc-lemma r)))
        (sym (ren-comp-formula (extend-ren suc) (extend-ren (extend-ren r))))
elim-renamings-commute {Φ = class Φ ∈ class Ψ} r =
  cong₂ (λ Ξ Ξ' → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ Ξ')) lemma (elim-renamings-commute {Φ = Ψ} (extend-ren r))
  where
    lemma :
      extend-formula-ctx (elim (ren-Formula (extend-ren r) Φ))
        ≡
      ren-formula (extend-ren (extend-ren r)) (extend-formula-ctx (elim Φ))
    lemma =
      trans
        (trans
          (trans
            (cong (λ φ → extend-formula-ctx φ) (elim-renamings-commute {Φ = Φ} (extend-ren r)))
            (ren-comp-formula (extend-ren r) (extend-ren suc)))
          (cong (λ r' → ren-formula r' (elim Φ)) (extend-suc-lemma r)))
        (sym (ren-comp-formula (extend-ren suc) (extend-ren (extend-ren r))))
elim-renamings-commute {Φ = Φ ∧ Ψ} r = cong₂ _∧_ (elim-renamings-commute {Φ = Φ} r) (elim-renamings-commute {Φ = Ψ} r)
elim-renamings-commute {Φ = Φ ⇒ Ψ} r = cong₂ _⇒_ (elim-renamings-commute {Φ = Φ} r) (elim-renamings-commute {Φ = Ψ} r)
elim-renamings-commute {Φ = Φ ⇔ Ψ} r = cong₂ _⇔_ (elim-renamings-commute {Φ = Φ} r) (elim-renamings-commute {Φ = Ψ} r)
elim-renamings-commute {Φ = all Φ} r = cong all (elim-renamings-commute {Φ = Φ} (extend-ren r))
elim-renamings-commute {Φ = exists Φ} r = cong exists (elim-renamings-commute {Φ = Φ} (extend-ren r))

elim-extend-commute : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → elim (extend-Formula-ctx Φ) ≡ extend-formula-ctx (elim Φ)
elim-extend-commute {Φ = Φ} = elim-renamings-commute {Φ = Φ} (extend-ren suc)