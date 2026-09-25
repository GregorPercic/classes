open import Syntax public
open import Substitutions public


elim : ∀ {Γ} → Formula₀ Γ → formula Γ
elim ⊥ = ⊥
elim (svar x ≈ svar y) = svar x ≈ svar y
elim (svar x ≈ class Φ) = all (svar zero ∈ svar (suc x) ⇔ elim Φ)
elim (class Φ ≈ svar x) = all (elim Φ ⇔ svar zero ∈ svar (suc x))
elim (class Φ ≈ class Ψ) = all (elim Φ ⇔ elim Ψ)
elim (svar x ∈ svar y) = svar x ∈ svar y
elim (svar x ∈ class Φ) = (elim Φ) [ svar x ]f
elim (class Φ ∈ svar x) =
  exists (all
    (svar zero ∈ svar (suc zero)
      ⇔
    extend-ren-suc-formula (elim Φ)) ∧ svar zero ∈ svar (suc x))
elim (class Φ ∈ class Ψ) =
  exists (all
    (svar zero ∈ svar (suc zero)
      ⇔
    extend-ren-suc-formula (elim Φ)) ∧ elim Ψ)
elim (Φ ∧ Ψ) = elim Φ ∧ elim Ψ
elim (Φ ⇒ Ψ) = elim Φ ⇒ elim Ψ
elim (Φ ⇔ Ψ) = elim Φ ⇔ elim Ψ
elim (all Φ) = all (elim Φ)
elim (exists Φ) = exists (elim Φ)

extend-suc-lemma : ∀ {Γ Δ} (r : ren Γ Δ) →
  (extend-ren suc) ∘ (extend-ren r) ≡ (extend-ren (extend-ren r)) ∘ (extend-ren suc)
extend-suc-lemma r = fun-ext λ {zero → refl ; (suc x) → refl}

elim-ren : ∀ {Γ Δ} {Φ : Formula₀ Γ} (r : ren Γ Δ) →
  elim (ren-Formula r Φ) ≡ ren-formula r (elim Φ)
elim-ren {Φ = ⊥} r = refl
elim-ren {Φ = svar x ≈ svar y} r = refl
elim-ren {Φ = svar x ≈ class Φ} r =
  cong (λ Ξ → all (svar zero ∈ svar (suc (r x)) ⇔ Ξ)) (elim-ren {Φ = Φ} (extend-ren r))
elim-ren {Φ = class Φ ≈ svar x} r =
  cong (λ Ξ → all (Ξ ⇔ svar zero ∈ svar (suc (r x)))) (elim-ren {Φ = Φ} (extend-ren r))
elim-ren {Φ = class Φ ≈ class Ψ} r =
  cong₂
    (λ Ξ Ξ' → all (Ξ ⇔ Ξ'))
    (elim-ren {Φ = Φ} (extend-ren r))
    (elim-ren {Φ = Ψ} (extend-ren r))
elim-ren {Φ = svar x ∈ svar y} r = refl
elim-ren {Φ = svar x ∈ class Φ} r =
  trans
    (trans
      (trans
        (cong
          (λ Ξ → ren-formula (ren₀ (r x)) Ξ)
          (elim-ren {Φ = Φ} (extend-ren r)))
        (ren-comp-formula (extend-ren r) (ren₀ (r x))))
      (cong (λ r' → ren-formula r' (elim Φ)) (ren₀-under-extend-comp-eq r)))
    (sym (ren-comp-formula (ren₀ x) r))
elim-ren {Φ = class Φ ∈ svar x} r =
  cong (λ Ξ → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ svar zero ∈ svar (suc (r x)))) lemma
  where
    lemma :
      extend-ren-suc-formula (elim (ren-Formula (extend-ren r) Φ))
        ≡
      ren-formula (extend-ren (extend-ren r)) (extend-ren-suc-formula (elim Φ))
    lemma =
      trans
        (trans
          (trans
            (cong (λ φ → extend-ren-suc-formula φ) (elim-ren {Φ = Φ} (extend-ren r)))
            (ren-comp-formula (extend-ren r) (extend-ren suc)))
          (cong (λ r' → ren-formula r' (elim Φ)) (extend-suc-lemma r)))
        (sym (ren-comp-formula (extend-ren suc) (extend-ren (extend-ren r))))
elim-ren {Φ = class Φ ∈ class Ψ} r =
  cong₂ (λ Ξ Ξ' → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ Ξ')) lemma (elim-ren {Φ = Ψ} (extend-ren r))
  where
    lemma :
      extend-ren-suc-formula (elim (ren-Formula (extend-ren r) Φ))
        ≡
      ren-formula (extend-ren (extend-ren r)) (extend-ren-suc-formula (elim Φ))
    lemma =
      trans
        (trans
          (trans
            (cong (λ φ → extend-ren-suc-formula φ) (elim-ren {Φ = Φ} (extend-ren r)))
            (ren-comp-formula (extend-ren r) (extend-ren suc)))
          (cong (λ r' → ren-formula r' (elim Φ)) (extend-suc-lemma r)))
        (sym (ren-comp-formula (extend-ren suc) (extend-ren (extend-ren r))))
elim-ren {Φ = Φ ∧ Ψ} r = cong₂ _∧_ (elim-ren {Φ = Φ} r) (elim-ren {Φ = Ψ} r)
elim-ren {Φ = Φ ⇒ Ψ} r = cong₂ _⇒_ (elim-ren {Φ = Φ} r) (elim-ren {Φ = Ψ} r)
elim-ren {Φ = Φ ⇔ Ψ} r = cong₂ _⇔_ (elim-ren {Φ = Φ} r) (elim-ren {Φ = Ψ} r)
elim-ren {Φ = all Φ} r = cong all (elim-ren {Φ = Φ} (extend-ren r))
elim-ren {Φ = exists Φ} r = cong exists (elim-ren {Φ = Φ} (extend-ren r))


-- Non-elim lemmas

subst-zero-eq-Formula : ∀ {C Γ} {Φ : Formula C (extend Γ)} → (extend-ren-suc-Formula Φ) [ svar zero ]F ≡ Φ
subst-zero-eq-Formula {Φ = Φ} = ren₀-zero-extend-ren-suc-inv-Formula

ren₀-inj-formula : ∀ {C Γ} {φ : formula (extend Γ)} {x : Var Γ} →
  ren-Formula {C = C} (ren₀ x) (inj-formula φ) ≡ inj-formula (ren-formula (ren₀ x) φ)
ren₀-inj-formula {x = x} = ren-inj-formula (ren₀ x)