open import Data.Product using (_×_ ; _,_)
open import Agda.Primitive using (_⊔_)

open import Proof
open import PProof
open import Theory
open import TTheory
open import Conservation-Lemmas


conservation-⇐ : ∀ {C Γ hyp} {φ : formula Γ} →
  proof ST hyp φ →
  Proof CT {C} {Γ} (inj-formula-l hyp) (inj-formula φ)
conservation-⇐ (axiom ext r) = all-i (all-i (axiom class≈class (λ {A → svar (suc zero) ; B → svar zero}) empty-ren))
conservation-⇐ (hyp-ax is-in) = Hyp-ax (inj-list-mem is-in)
conservation-⇐ lem = lem
conservation-⇐ ≈-i = ≈-i
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

conservation-⇒-main-theorem : ∀ {Γ Hyp} {Φ : Formula₀ Γ} →
  Proof CT {𝟘} {Γ} Hyp Φ →
  proof ST {Γ} (map elim Hyp) (elim Φ)
conservation-⇒-main-theorem (axiom (set∈class C Γ y Ψ) σ r) =
  Proof.eq-to-⇔ (lemma {y = y} {Φ = Ψ} {r = r} {σ = σ})
  where
    lemma : ∀ {C Γ Δ} {y : Var Γ} {Φ : Formula C (extend Γ)} {r : ren Γ Δ} {σ : Subst Δ C 𝟘} → 
      ren-formula (ren₀ (r y)) (elim (Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)))
        ≡
      elim (Subst-Formula σ (ren-Formula r (ren-Formula (ren₀ y) Φ)))
    lemma {Φ = Φ} {r = r} {σ = σ} =
      trans
        (sym (elim-subst {Φ = Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)}))
        (cong
          elim
          (trans
            (ren₀-under-extend-Subst-Formula {Φ = ren-Formula (extend-ren r) Φ} σ)
            (cong
              (λ Ξ → Subst-Formula σ Ξ)
              (ren₀-under-extend-ren r))))
conservation-⇒-main-theorem (axiom class∈class σ r) with σ A | σ B
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
conservation-⇒-main-theorem {Γ = Γ} (axiom class≈class σ r) with σ A | σ B
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
conservation-⇒-main-theorem (Hyp-ax is-in) = hyp-ax (elim-list-mem is-in)
conservation-⇒-main-theorem lem = lem
conservation-⇒-main-theorem (≈-i {t = svar x}) = ≈-i
conservation-⇒-main-theorem (≈-i {t = class Φ}) = all-⇔-refl
conservation-⇒-main-theorem (∧-i p p') = ∧-i (conservation-⇒-main-theorem p) (conservation-⇒-main-theorem p')
conservation-⇒-main-theorem (⇒-i p) = ⇒-i (conservation-⇒-main-theorem p)
conservation-⇒-main-theorem (⇔-i p p') = ⇔-i (conservation-⇒-main-theorem p) (conservation-⇒-main-theorem p')
conservation-⇒-main-theorem (all-i p) = all-i (transport-proof-hyp Hyp-elim-lemma (conservation-⇒-main-theorem p))
conservation-⇒-main-theorem (exists-i t p) = exists-i t (transport-proof (elim-subst {t = t}) (conservation-⇒-main-theorem p))
conservation-⇒-main-theorem (⊥-e p) = ⊥-e (conservation-⇒-main-theorem p)
conservation-⇒-main-theorem (∧-e-l p) = ∧-e-l (conservation-⇒-main-theorem p)
conservation-⇒-main-theorem (∧-e-r p) = ∧-e-r (conservation-⇒-main-theorem p)
conservation-⇒-main-theorem (⇒-e p p') = ⇒-e (conservation-⇒-main-theorem p) (conservation-⇒-main-theorem p')
conservation-⇒-main-theorem (⇔-e-lr p) = ⇔-e-lr (conservation-⇒-main-theorem p)
conservation-⇒-main-theorem (⇔-e-rl p) = ⇔-e-rl (conservation-⇒-main-theorem p)
conservation-⇒-main-theorem (exists-e {Ψ = Ψ} p p') =
  exists-e
    (conservation-⇒-main-theorem p)
    (transport-proof-hyp
      (cong₂ _∷_ Hyp-elim-lemma refl)
      (transport-proof
        (elim-ren {Φ = Ψ} suc)
        (conservation-⇒-main-theorem p')))
conservation-⇒-main-theorem (all-e t p) = transport-proof (sym (elim-subst {t = t})) (all-e t (conservation-⇒-main-theorem p))
conservation-⇒-main-theorem (≈-e {t = t} {u = u} eq p) =
  transport-proof
    (sym (elim-subst {t = u}))
    (≈-e {t = t} {u = u}
      (transport-proof
        elim-inj-inv
        (conservation-⇒-main-theorem eq))
      (transport-proof
        (elim-subst {t = t})
        (conservation-⇒-main-theorem p)))

conservation-⇒ : ∀ {C Γ hyp} {φ : formula Γ} →
  Proof CT {C} {Γ} (inj-formula-l hyp) (inj-formula φ) →
  proof ST {Γ} hyp φ
conservation-⇒ {hyp = hyp} {φ = φ} p =
  transport-proof-hyp
    lemma2
    (transport-proof
      lemma1
      (conservation-⇒-main-theorem (Subst-Proof magic-Subst p)))
  where
    lemma1 : ∀ {Γ} {φ : formula Γ} → elim (Subst-Formula magic-Subst (inj-formula φ)) ≡ φ
    lemma1 {φ = φ} =
      trans
        (cong elim (inj-formula-Subst-id {φ = φ} magic-Subst))
        elim-inj-inv

    lemma2 : ∀ {Γ} {hyp : List (formula Γ)} → map elim (map (Subst-Formula magic-Subst) (inj-formula-l hyp)) ≡ hyp
    lemma2 {hyp = []} = refl
    lemma2 {hyp = φ ∷l hyp} = cong₂ _∷l_ lemma1 lemma2


-- The Conservation Theorem

_↔_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
ty ↔ ty' = (ty → ty') × (ty' → ty)

-- The (⇐) direction of the theorem can also be seen as a kind of Soundness theorem.
-- In that case, the (⇒) direction alone is the Conservation theorem proper.

conservation : ∀ {C Γ hyp} (φ : formula Γ) →
  Proof CT {C} {Γ} (inj-formula-l hyp) (inj-formula φ)
    ↔
  proof ST {Γ} hyp φ
conservation φ = conservation-⇒ , conservation-⇐

conservation-corollary : ∀ {C Γ} (φ : formula Γ) →
  Proof CT {C} {Γ} [] (inj-formula φ) ↔ proof ST {Γ} [] φ
conservation-corollary φ = conservation φ