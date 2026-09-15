open import Syntax public
open import Substitutions public
open import Proof
open import PProof
open import Eliminability-Lemmas public


inj-formula-l : ∀ {C Γ} → List (formula Γ) → List (Formula C Γ)
inj-formula-l = map inj-formula

inj-list-mem : ∀ {C Γ hyp} {φ : formula Γ} → hyp ∋ φ → map (inj-formula {C = C}) hyp ∋ inj-formula φ
inj-list-mem here = here
inj-list-mem (there is-in) = there (inj-list-mem is-in)

inj-formula-l-lemma : ∀ {C Γ} {hyp : List (formula Γ)} →
  inj-formula-l {C = C} (Proof.weaken-l hyp) ≡ PProof.weaken-l (inj-formula-l hyp)
inj-formula-l-lemma {hyp = []} = refl
inj-formula-l-lemma {hyp = φ ∷l hyp} = cong₂ _∷l_ (sym (ren-inj-formula suc)) inj-formula-l-lemma

inj-formula-subst : ∀ {C Γ} {t : term Γ} {φ : formula (extend Γ)} →
  inj-formula {C = C} (φ [ t ]f) ≡ (inj-formula φ) [ t ]F
inj-formula-subst {t = svar x} = sym (ren-inj-formula (ren₀ x))

elim-list-mem : ∀ {Γ Hyp} {Φ : Formula₀ Γ} → Hyp ∋ Φ → map elim Hyp ∋ elim Φ
elim-list-mem here = here
elim-list-mem (there is-in) = there (elim-list-mem is-in)

Hyp-elim-lemma : ∀ {Γ} {Hyp : List (Formula₀ Γ)} → map elim (PProof.weaken-l Hyp) ≡ Proof.weaken-l (map elim Hyp)
Hyp-elim-lemma {Hyp = []} = refl
Hyp-elim-lemma {Hyp = Φ ∷l Hyp} = cong₂ _∷l_ (elim-ren {Φ = Φ} suc) Hyp-elim-lemma

elim-subst : ∀ {Γ} {t : term Γ} {Φ : Formula₀ (extend Γ)} → elim (Φ [ t ]F) ≡ (elim Φ) [ t ]f
elim-subst {t = svar x} {Φ = Φ} = elim-ren {Φ = Φ} (ren₀ x)

elim-inj-inv : ∀ {Γ} {φ : formula Γ} → elim (inj-formula φ) ≡ φ
elim-inj-inv {φ = ⊥} = refl
elim-inj-inv {φ = svar x ≈ svar y} = refl
elim-inj-inv {φ = svar x ∈ svar y} = refl
elim-inj-inv {φ = φ ∧ ψ} = cong₂ _∧_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = φ ⇒ ψ} = cong₂ _⇒_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = φ ⇔ ψ} = cong₂ _⇔_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = all φ} = cong all elim-inj-inv
elim-inj-inv {φ = exists φ} = cong exists elim-inj-inv

subst-elim-extend-ren-eq : ∀ {Γ} {Φ : Formula₀ (extend Γ)} →
  ren-formula (ren₀ zero) (elim (ren-Formula (extend-ren suc) Φ)) ≡ elim Φ
subst-elim-extend-ren-eq {Φ = Φ} =
  trans
    (sym (elim-ren {Φ = ren-Formula (extend-ren suc) Φ} (ren₀ zero)))
    (trans
      (cong elim (ren-comp-Formula {Φ = Φ} (extend-ren suc) (ren₀ zero)))
      (trans
        (cong (λ r → elim (ren-Formula r Φ)) ren₀-zero-extend-ren-suc-inv)
        (cong elim (id-ren-Formula {Φ = Φ}))))

magic-Subst : ∀ {C D Γ} → Subst Γ C D
magic-Subst _ = class ⊥

inj-formula-Subst-id : ∀ {C D Γ} {φ : formula Γ} (σ : Subst Γ C D) → Subst-Formula σ (inj-formula φ) ≡ inj-formula {C = D} φ
inj-formula-Subst-id {φ = ⊥} σ = refl
inj-formula-Subst-id {φ = svar x ≈ svar y} σ = refl
inj-formula-Subst-id {φ = svar x ∈ svar y} σ = refl
inj-formula-Subst-id {φ = φ ∧ ψ} σ = cong₂ _∧_ (inj-formula-Subst-id σ) (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = φ ⇒ ψ} σ = cong₂ _⇒_ (inj-formula-Subst-id σ) (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = φ ⇔ ψ} σ = cong₂ _⇔_ (inj-formula-Subst-id σ) (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = all φ} σ = cong all (inj-formula-Subst-id (extend-Subst σ))
inj-formula-Subst-id {φ = exists φ} σ = cong exists (inj-formula-Subst-id (extend-Subst σ))