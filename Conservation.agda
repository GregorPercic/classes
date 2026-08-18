open import Data.Product using (_×_ ; _,_)
open import Agda.Primitive using (_⊔_)

open import Syntax
open import Substitutions
open import Proof
open import PProof
open import Theory
open import TTheory
open import Eliminability-Lemmas


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
  inj-formula {C = C} (φ [ t ]f) ≡ (inj-formula φ [ t ]F)
inj-formula-subst {t = svar x} = sym (ren-inj-formula (ren₀ x))

conservation-⇐ : ∀ {C Γ hyp} {φ : formula Γ} → proof ST hyp φ → Proof CT {C} {Γ} (inj-formula-l hyp) (inj-formula φ)
conservation-⇐ (axiom ext r) = all-i (all-i (axiom class≈class (λ {A → svar (suc zero) ; B → svar zero}) empty-ren))
conservation-⇐ (hyp-ax is-in) = Hyp-ax (inj-list-mem is-in)
conservation-⇐ ≈-refl = ≈-refl
conservation-⇐ (∧-i p p') = ∧-i (conservation-⇐ p) (conservation-⇐ p')
conservation-⇐ (⇒-i p) = ⇒-i (conservation-⇐ p)
conservation-⇐ (⇔-i p p') = ⇔-i (conservation-⇐ p) (conservation-⇐ p')
conservation-⇐ (all-i p) = all-i (transport-Proof-Hyp inj-formula-l-lemma (conservation-⇐ p))
conservation-⇐ (exists-i t p) = exists-i t (transport-Proof (inj-formula-subst {t = t}) (conservation-⇐ p))
conservation-⇐ (⊥-e p) = ⊥-e (conservation-⇐ p)
conservation-⇐ (∧-e-l p) = ∧-e-l (conservation-⇐ p)
conservation-⇐ (∧-e-r p) = ∧-e-r (conservation-⇐ p)
conservation-⇐ (⇒-e p p') = ⇒-e (conservation-⇐ p) (conservation-⇐ p')
conservation-⇐ (⇔-e-lr p) = ⇔-e-lr (conservation-⇐ p)
conservation-⇐ (⇔-e-rl p) = ⇔-e-rl (conservation-⇐ p)
conservation-⇐ (exists-e p p') =
  exists-e
    (conservation-⇐ p)
    (transport-Proof-Hyp
      (cong₂ _∷_ inj-formula-l-lemma refl)
      (transport-Proof
        (sym (ren-inj-formula suc))
        (conservation-⇐ p')))
conservation-⇐ (all-e t p) = transport-Proof (sym (inj-formula-subst {t = t})) (all-e t (conservation-⇐ p))
conservation-⇐ (≈-e {t = t} {u = u} p p') =
  transport-Proof
    (sym (inj-formula-subst {t = u}))
    (≈-e
      (conservation-⇐ p)
      (transport-Proof
        (inj-formula-subst {t = t})
        (conservation-⇐ p')))

elim-list-mem : ∀ {Γ Hyp} {Φ : Formula₀ Γ} → Hyp ∋ Φ → map elim Hyp ∋ elim Φ
elim-list-mem here = here
elim-list-mem (there is-in) = there (elim-list-mem is-in)

Hyp-elim-lemma : ∀ {Γ} {Hyp : List (Formula₀ Γ)} → map elim (PProof.weaken-l Hyp) ≡ Proof.weaken-l (map elim Hyp)
Hyp-elim-lemma {Hyp = []} = refl
Hyp-elim-lemma {Hyp = Φ ∷l Hyp} = cong₂ _∷l_ (elim-ren {Φ = Φ} suc) Hyp-elim-lemma

elim-subst : ∀ {Γ} {t : term Γ} {Φ : Formula₀ (extend Γ)} → elim (Φ [ t ]F) ≡ (elim Φ [ t ]f)
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

conservation-⇒-lemma : ∀ {Γ Hyp} {Φ : Formula₀ Γ} → Proof CT {𝟘} {Γ} Hyp Φ → proof ST {Γ} (map elim Hyp) (elim Φ)
conservation-⇒-lemma (axiom (set∈class C Γ y Ψ) σ r) =
  Proof.eq-to-⇔ (lemma {y = y} {Φ = Ψ} {r = r} {σ = σ})
  where
    lemma : ∀ {C Γ Δ} {y : Var Γ} {Φ : Formula C (extend Γ)} {r : ren Γ Δ} {σ : Subst Δ C 𝟘} → 
      ren-formula (ren₀ (r y)) (elim (Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)))
        ≡
      elim (Subst-Formula σ (ren-Formula r (ren-Formula (ren₀ y) Φ)))
    lemma {Φ = Φ} {r = r} {σ = σ} =
      trans
        (sym (elim-subst {Φ = Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)}))
        (cong elim
          (trans
            (ren₀-under-extend-Subst-Formula {Φ = ren-Formula (extend-ren r) Φ} σ)
            (cong
              (λ Ξ → Subst-Formula σ Ξ)
              (ren₀-under-extend-ren r))))
conservation-⇒-lemma (axiom class∈class σ r) with σ A | σ B
... | svar x  | svar y = Proof.conservation-equiv
... | svar x  | class Φ =
  transport-proof
    (cong (λ Ξ → (ren-formula (ren₀ x) (elim Φ) ⇔ exists (svar zero ≈ svar (suc x) ∧ Ξ)))
      (sym (subst-elim-extend-ren-eq {Φ = Φ})))
    Proof.conservation-equiv
... | class Φ | svar x =
  Proof.eq-to-⇔
    (cong
      (λ Ξ → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ svar zero ∈ svar (suc x)))
      (sym (elim-ren {Φ = Φ} (extend-ren suc))))
... | class Φ | class Ψ =
  Proof.eq-to-⇔
    (cong₂
      (λ Ξ Ξ' → exists (all (svar zero ∈ svar (suc zero) ⇔ Ξ) ∧ Ξ'))
      (sym (elim-ren {Φ = Φ} (extend-ren suc)))
      (sym (subst-elim-extend-ren-eq {Φ = Ψ})))
conservation-⇒-lemma {Γ = Γ} (axiom class≈class σ r) with σ A | σ B
... | svar x  | svar y = all-e (svar y) (all-e (svar x) (axiom ext empty-ren))
... | svar x  | class Φ =
  Proof.eq-to-⇔
    (cong
      (λ Ξ → all (svar zero ∈ svar (suc x) ⇔ Ξ))
      (sym (subst-elim-extend-ren-eq {Φ = Φ})))
... | class Φ | svar x =
  Proof.eq-to-⇔
    (cong
      (λ Ξ → all (Ξ ⇔ svar zero ∈ svar (suc x)))
      (sym (subst-elim-extend-ren-eq {Φ = Φ})))
... | class Φ | class Ψ =
  Proof.eq-to-⇔
    (cong₂
      (λ Ξ Ξ' → all (Ξ ⇔ Ξ'))
      (sym (subst-elim-extend-ren-eq {Φ = Φ}))
      (sym (subst-elim-extend-ren-eq {Φ = Ψ})))
conservation-⇒-lemma (Hyp-ax is-in) = hyp-ax (elim-list-mem is-in)
conservation-⇒-lemma (≈-refl {t = svar x}) = ≈-refl
conservation-⇒-lemma (≈-refl {t = class Φ}) = all-⇔-refl
conservation-⇒-lemma (∧-i p p') = ∧-i (conservation-⇒-lemma p) (conservation-⇒-lemma p')
conservation-⇒-lemma (⇒-i p) = ⇒-i (conservation-⇒-lemma p)
conservation-⇒-lemma (⇔-i p p') = ⇔-i (conservation-⇒-lemma p) (conservation-⇒-lemma p')
conservation-⇒-lemma (all-i p) = all-i (transport-proof-hyp Hyp-elim-lemma (conservation-⇒-lemma p))
conservation-⇒-lemma (exists-i t p) = exists-i t (transport-proof (elim-subst {t = t}) (conservation-⇒-lemma p))
conservation-⇒-lemma (⊥-e p) = ⊥-e (conservation-⇒-lemma p)
conservation-⇒-lemma (∧-e-l p) = ∧-e-l (conservation-⇒-lemma p)
conservation-⇒-lemma (∧-e-r p) = ∧-e-r (conservation-⇒-lemma p)
conservation-⇒-lemma (⇒-e p p') = ⇒-e (conservation-⇒-lemma p) (conservation-⇒-lemma p')
conservation-⇒-lemma (⇔-e-lr p) = ⇔-e-lr (conservation-⇒-lemma p)
conservation-⇒-lemma (⇔-e-rl p) = ⇔-e-rl (conservation-⇒-lemma p)
conservation-⇒-lemma (exists-e {Ψ = Ψ} p p') =
  exists-e
    (conservation-⇒-lemma p)
    (transport-proof-hyp
      (cong₂ _∷_ Hyp-elim-lemma refl)
      (transport-proof
        (elim-ren {Φ = Ψ} suc)
        (conservation-⇒-lemma p')))
conservation-⇒-lemma (all-e t p) = transport-proof (sym (elim-subst {t = t})) (all-e t (conservation-⇒-lemma p))
conservation-⇒-lemma (≈-e {t = t} {u = u} eq p) =
  transport-proof
    (sym (elim-subst {t = u}))
    (≈-e {t = t} {u = u}
      (transport-proof
        elim-inj-inv
        (conservation-⇒-lemma eq))
      (transport-proof
        (elim-subst {t = t})
        (conservation-⇒-lemma p)))

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

conservation-⇒ : ∀ {C Γ hyp} {φ : formula Γ} → Proof CT {C = C} (inj-formula-l hyp) (inj-formula φ) → proof ST hyp φ
conservation-⇒ {hyp = hyp} {φ = φ} p =
  transport-proof-hyp
    lemma2
    (transport-proof
      lemma1
      (conservation-⇒-lemma (Subst-Proof magic-Subst p)))
  where
    lemma1 : ∀ {Γ} {φ : formula Γ} → elim (Subst-Formula magic-Subst (inj-formula φ)) ≡ φ
    lemma1 {φ = φ} =
      trans
        (cong elim (inj-formula-Subst-id {φ = φ} magic-Subst))
        elim-inj-inv

    lemma2 : ∀ {Γ} {hyp : List (formula Γ)} → map elim (map (Subst-Formula magic-Subst) (inj-formula-l hyp)) ≡ hyp
    lemma2 {hyp = []} = refl
    lemma2 {hyp = φ ∷l hyp} = cong₂ _∷l_ lemma1 lemma2


-- The Conservation theorem

_↔_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
ty ↔ ty' = (ty → ty') × (ty' → ty)

-- The (⇐) direction of the theorem can also seen as a kind of Soundness theorem.
-- In that case, the (⇒) direction alone is the Conservation theorem proper.

conservation : ∀ {C Γ hyp} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula-l hyp) (inj-formula φ) ↔ proof ST {Γ} hyp φ
conservation φ = conservation-⇒ , conservation-⇐

conservation-corollary : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} [] (inj-formula φ) ↔ proof ST {Γ} [] φ
conservation-corollary φ = conservation φ