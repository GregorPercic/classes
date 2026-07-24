open import Data.Product

open import Syntax
open import Substitutions
open import Proof
open import Theory
open import Eliminability

open import Agda.Primitive


_↔_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
ty ↔ ty' = (ty → ty') × (ty' → ty)

transport-proof : ∀ {T C Γ} {Φ Ψ : Formula C Γ} → (Φ ≡ Ψ) → Proof T Φ → Proof T Ψ
transport-proof {T = T} e p = ≡-subst (λ Ξ → Proof T Ξ) e p

-- r-inj-∧ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ∧ Ψ ≡ Φ' ∧ Ψ') → Ψ ≡ Ψ'
-- r-inj-∧ refl = refl
-- 
-- l-inj-∧ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ∧ Ψ ≡ Φ' ∧ Ψ') → Φ ≡ Φ'
-- l-inj-∧ refl = refl
-- 
-- r-inj-⇔ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ⇔ Ψ) ≡ (Φ' ⇔ Ψ') → Ψ ≡ Ψ'
-- r-inj-⇔ refl = refl
-- 
-- l-inj-⇔ : ∀ {C Γ} {Φ Ψ Φ' Ψ' : Formula C Γ} → (Φ ⇔ Ψ) ≡ (Φ' ⇔ Ψ') → Φ ≡ Φ'
-- l-inj-⇔ refl = refl
-- 
-- inj-¬ : ∀ {C Γ} {Φ Φ' : Formula C Γ} → ¬ Φ ≡ ¬ Φ' → Φ ≡ Φ'
-- inj-¬ refl = refl
-- 
-- inj-all : ∀ {C Γ} {Φ Φ' : Formula C (extend Γ)} → all Φ ≡ all Φ' → Φ ≡ Φ'
-- inj-all refl = refl
-- 
-- inj-exists : ∀ {C Γ} {Φ Φ' : Formula C (extend Γ)} → exists Φ ≡ exists Φ' → Φ ≡ Φ'
-- inj-exists refl = refl
-- 
-- l-inj-≈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ≈ t') ≡ (u ≈ u') → t ≡ u
-- l-inj-≈ refl = refl
-- 
-- r-inj-≈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ≈ t') ≡ (u ≈ u') → t' ≡ u'
-- r-inj-≈ refl = refl
-- 
-- l-inj-∈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ∈ t') ≡ (u ∈ u') → t ≡ u
-- l-inj-∈ refl = refl
-- 
-- r-inj-∈ : ∀ {C Γ} {t t' u u' : Term C Γ} → (t ∈ t') ≡ (u ∈ u') → t' ≡ u'
-- r-inj-∈ refl = refl
-- 
-- 
-- inj-formula-injective : ∀ {C Γ} {φ ψ : formula Γ} → inj-formula {C = C} φ ≡ inj-formula ψ → φ ≡ ψ
-- inj-formula-injective {φ = svar x ≈ svar y} {ψ = svar x' ≈ svar y'} refl = refl
-- inj-formula-injective {φ = svar x ∈ svar y} {ψ = svar x' ∈ svar y'} refl = refl
-- inj-formula-injective {φ = φ ∧ φ'} {ψ = ψ ∧ ψ'} e = cong₂ _∧_ (inj-formula-injective (l-inj-∧ e)) (inj-formula-injective (r-inj-∧ e))
-- inj-formula-injective {φ = φ ⇔ φ'} {ψ = ψ ⇔ ψ'} e = cong₂ _⇔_ (inj-formula-injective (l-inj-⇔ e)) (inj-formula-injective (r-inj-⇔ e))
-- inj-formula-injective {φ = ¬ φ} {ψ = ¬ ψ} e = cong ¬_ (inj-formula-injective (inj-¬ e))
-- inj-formula-injective {φ = all φ} {ψ = all ψ} e = cong all (inj-formula-injective (inj-all e))
-- inj-formula-injective {φ = exists φ} {ψ = exists ψ} e = cong exists (inj-formula-injective (inj-exists e))

conservation-⇐-lemma : ∀ {Γ} {Φ : Formula₀ Γ} → Proof ST {𝟘} {Γ} Φ → Proof CT {𝟘} {Γ} Φ
conservation-⇐-lemma (axiom (ext Γ x y) σ r) =
  Subst-Proof σ (ren-Proof r (axiom class≈class (λ {A → svar x ; B → svar y}) empty-ren))
conservation-⇐-lemma (axiom (in-equiv Γ x y) σ r) =
  Subst-Proof σ (ren-Proof r (axiom class∈class (λ {A → svar x ; B → svar y}) empty-ren))
conservation-⇐-lemma ⇔-refl = ⇔-refl
conservation-⇐-lemma (∧-cong p p') = ∧-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (⇔-cong p p') = ⇔-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (¬-cong p) = ¬-cong (conservation-⇐-lemma p)
conservation-⇐-lemma (all-cong p) = all-cong (conservation-⇐-lemma p)
conservation-⇐-lemma (⇔-trans p p') = ⇔-trans (conservation-⇐-lemma p) (conservation-⇐-lemma p')
conservation-⇐-lemma (exists-cong p) = exists-cong (conservation-⇐-lemma p)
conservation-⇐-lemma (axiom (tmp C Γ x Φ) σ r) = axiom (tmp C Γ x Φ) σ r

conservation-⇐ : ∀ {C Γ} (φ : formula Γ) → Proof ST {𝟘} {Γ} (inj-formula φ) → Proof CT {C} {Γ} (inj-formula φ)
conservation-⇐ φ p =
  transport-proof
    Subst-empty-id
    (Subst-Proof empty-Subst (conservation-⇐-lemma {Φ = inj-formula φ} p))

-- svar-injective : ∀ {C Γ} {x y : Var Γ} → Term.svar {C = C} x ≡ svar y → x ≡ y
-- svar-injective refl = refl

magic-Subst : ∀ {C D Γ} → Subst Γ C D
magic-Subst _ = class (svar zero ≈ svar zero)

inj-formula-Subst-id : ∀ {C D Γ} {φ : formula Γ} (σ : Subst Γ C D) → Subst-Formula σ (inj-formula φ) ≡ inj-formula {C = D} φ
inj-formula-Subst-id {φ = svar x ≈ svar y} σ = refl
inj-formula-Subst-id {φ = svar x ∈ svar y} σ = refl
inj-formula-Subst-id {φ = φ ∧ ψ} σ = cong₂ _∧_ (inj-formula-Subst-id σ) (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = φ ⇔ ψ} σ = cong₂ _⇔_ (inj-formula-Subst-id σ) (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = ¬ φ} σ = cong ¬_ (inj-formula-Subst-id σ)
inj-formula-Subst-id {φ = all φ} σ = cong all (inj-formula-Subst-id (extend-Subst σ))
inj-formula-Subst-id {φ = exists φ} σ = cong exists (inj-formula-Subst-id (extend-Subst σ))

-- Lemma : ∀ {C Γ} {φ : formula Γ} {Φ : Formula C Γ} → (Φ ≡ inj-formula φ) → Proof CT {C} {Γ} Φ → Proof ST {𝟘} {Γ} (inj-formula φ)
-- Lemma {φ = svar x ∈ svar x' ⇔ ψ} () (axiom (set∈class C Γ y Φ) σ r)
-- Lemma {φ = svar x ∈ svar y ⇔ exists (svar zero ≈ svar x' ∧ svar zero ∈ svar y')} e (axiom class∈class σ r) =
--   ≡-subst₂
--     (λ t u → Proof ST (svar x ∈ svar y ⇔ exists (svar zero ≈ t ∧ svar zero ∈ u)))
--     lemma3
--     lemma4
--     {!   !}
--   where
--     lemma1 : σ A ≡ svar x
--     lemma1 = l-inj-∈ (l-inj-⇔ e)
-- 
--     lemma2 : σ B ≡ svar y
--     lemma2 = r-inj-∈ (l-inj-⇔ e)
-- 
--     lemma3-1 : extend-Subst σ A ≡ svar x'
--     lemma3-1 = r-inj-≈ (l-inj-∧ (inj-exists (r-inj-⇔ e)))
-- 
--     lemma3-2 : extend-Subst σ A ≡ svar (suc x)
--     lemma3-2 = cong (λ t → ren-Term suc t) lemma1
-- 
--     -- we also do conversion from C to 𝟘 by descending to variable names
--     lemma3 : svar (suc x) ≡ svar x'
--     lemma3 = cong svar (svar-injective (trans (sym lemma3-2) lemma3-1))
-- 
--     lemma4-1 : extend-Subst σ B ≡ svar y'
--     lemma4-1 = r-inj-∈ (r-inj-∧ (inj-exists (r-inj-⇔ e)))
-- 
--     lemma4-2 : extend-Subst σ B ≡ svar (suc y)
--     lemma4-2 = cong (λ t → ren-Term suc t) lemma2
-- 
--     lemma4 : svar (suc y) ≡ svar y'
--     lemma4 = cong svar (svar-injective (trans (sym lemma4-2) lemma4-1))
-- Lemma {φ = svar x ≈ svar y ⇔ all (svar zero ∈ svar x' ⇔ svar zero ∈ svar y')} e (axiom class≈class σ r) = {!   !}
-- Lemma {φ = φ ⇔ φ'} e ⇔-refl =
--   eq-to-⇔
--     (cong
--       inj-formula
--       (inj-formula-injective
--         (trans (sym (l-inj-⇔ e)) (r-inj-⇔ e))))
-- Lemma {φ = φ ∧ φ' ⇔ ψ ∧ ψ'} refl (∧-cong p p') = ∧-cong (Lemma refl p) (Lemma refl p')
-- Lemma {φ = (φ ⇔ φ') ⇔ (ψ ⇔ ψ')} refl (⇔-cong p p') = ⇔-cong (Lemma refl p) (Lemma refl p')
-- Lemma {φ = ¬ φ ⇔ ¬ ψ} refl (¬-cong p) = ¬-cong (Lemma refl p)
-- Lemma {φ = all φ ⇔ all ψ} refl (all-cong p) = all-cong (Lemma refl p)
-- Lemma {φ = φ ⇔ ψ} refl (⇔-trans {Φ' = Φ'} p p') with existential-eliminability _ Φ' magic-Subst
-- ... | θ , equiv = {!   !}
-- --  ⇔-trans
-- --    -- termination check fails here
-- --    (Lemma refl (≡-subst (λ Ξ → Proof CT (Ξ ⇔ _)) (inj-formula-Subst-id magic-Subst) (⇔-trans (Subst-Proof magic-Subst p) equiv)))
-- --    {!   !}
-- Lemma {φ = exists φ ⇔ exists ψ} refl (exists-cong p) = exists-cong (Lemma refl p)
-- 
-- Lemma' : ∀ {C Γ} {φ : formula Γ} {Φ : Formula C Γ} → Proof CT (Φ ⇔ inj-formula φ) → Proof CT {C} {Γ} Φ → Proof ST {𝟘} {Γ} (inj-formula φ)
-- Lemma' eq p = {!   !}
-- 
-- conservation-⇒ : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
-- conservation-⇒ φ p = Lemma refl p
-- 
-- conservation-⇒' : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
-- conservation-⇒' φ p = Lemma' ⇔-refl p


elim-inj-inv : ∀ {Γ} {φ : formula Γ} → elim (inj-formula φ) ≡ φ
elim-inj-inv {φ = svar x ≈ svar y} = refl
elim-inj-inv {φ = svar x ∈ svar y} = refl
elim-inj-inv {φ = φ ∧ ψ} = cong₂ _∧_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = φ ⇔ ψ} = cong₂ _⇔_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = ¬ φ} = cong ¬_ elim-inj-inv
elim-inj-inv {φ = all φ} = cong all elim-inj-inv
elim-inj-inv {φ = exists φ} = cong exists elim-inj-inv

inj-elim-inj : ∀ {C Γ} {φ : formula Γ} → inj-formula {C = C} (elim (inj-formula φ)) ≡ inj-formula φ
inj-elim-inj = cong inj-formula elim-inj-inv

subst-extend-elim-eq : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → ren-formula (ren₀ zero) (elim (ren-Formula (extend-ren suc) Φ)) ≡ elim Φ
subst-extend-elim-eq {Φ = Φ} =
  trans
    (sym (elim-renamings-commute {Φ = ren-Formula (extend-ren suc) Φ} (ren₀ zero)))
    (trans
      (cong elim (ren-comp-Formula {Φ = Φ} (extend-ren suc) (ren₀ zero)))
      (trans
        (cong (λ r → elim (ren-Formula r Φ)) ren-zero-extend-ctx-id)
        (cong elim (id-ren-Formula {Φ = Φ}))))

ren₀-suc-eq-Term : ∀ {C Γ} {x : Var Γ} {t : Term C Γ} → ren-Term (ren₀ x) (ren-Term suc t) ≡ t
ren₀-suc-eq-Term {x = x} {t = t} =
  trans
    (ren-comp-Term suc (ren₀ x))
    (trans
      (cong (λ r' → ren-Term r' t) (lemma {x = x}))
      id-ren-Term)
  where
    lemma : ∀ {Γ} {x : Var Γ} → (ren₀ x) ∘ suc ≡ id-ren
    lemma = fun-ext (λ {zero → refl ; (suc y) → refl})

ren₀-extend-Subst-is-Subst-Formula : ∀ {C D Γ} {x : Var Γ} {Φ : Formula C Γ} (σ : Subst Γ C D) →
  Subst-Formula (comp-rS (ren₀ x) (extend-Subst σ)) Φ ≡ Subst-Formula σ Φ
ren₀-extend-Subst-is-Subst-Formula {Φ = Φ} σ = cong (λ σ' → Subst-Formula σ' Φ) (lemma σ)
  where
    lemma : ∀ {C D Γ} {x : Var Γ} (σ : Subst Γ C D) → comp-rS (ren₀ x) (extend-Subst σ) ≡ σ
    lemma σ = fun-ext λ c → ren₀-suc-eq-Term

ren₀-under-extend-Subst-Formula : ∀ {C D Γ} {x : Var Γ} {Φ : Formula C (extend Γ)} (σ : Subst Γ C D) →
  ren-Formula (ren₀ x) (Subst-Formula (extend-Subst σ) Φ) ≡ Subst-Formula σ (ren-Formula (ren₀ x) Φ)
ren₀-under-extend-Subst-Formula {x = x} σ =
  trans
    (comp-rS-Formula (extend-Subst σ) (ren₀ x))
    (ren₀-extend-Subst-is-Subst-Formula σ)

ren₀-under-extend-comp-eq : ∀ {Γ Δ} {x : Var Γ} (r : ren Γ Δ) → (ren₀ (r x)) ∘ (extend-ren r) ≡ r ∘ (ren₀ x)
ren₀-under-extend-comp-eq r = fun-ext λ {zero → refl ; (suc x) → refl}

ren₀-under-extend-ren : ∀ {C Γ Δ} {x : Var Γ} {Φ : Formula C (extend Γ)} (r : ren Γ Δ) →
  ren-Formula (ren₀ (r x)) (ren-Formula (extend-ren r) Φ) ≡ ren-Formula r (ren-Formula (ren₀ x) Φ)
ren₀-under-extend-ren {x = x} {Φ = Φ} r =
  trans
    (ren-comp-Formula (extend-ren r) (ren₀ (r x)))
    (trans
      (cong (λ r' → ren-Formula r' Φ) (ren₀-under-extend-comp-eq r))
      (sym (ren-comp-Formula (ren₀ x) r)))

weird-eq : ∀ {C : Set} {Γ} {x : Var Γ} {Φ : Formula₀ (extend Γ)} →
  _≡_ {a = lzero} {A = Formula C Γ}
    (inj-formula (ren-formula (ren₀ x) (elim Φ))
      ⇔
    exists (svar zero ≈ svar (suc x) ∧ inj-formula (ren-formula (ren₀ zero) (elim (ren-Formula (extend-ren suc) Φ)))))
    (ren-Formula (ren₀ x) (inj-formula (elim Φ))
      ⇔
    exists (svar zero ≈ svar (suc x) ∧ inj-formula (elim Φ)))
weird-eq {x = x} {Φ = Φ} =
  cong₂
    (λ Ξ Ξ' → Ξ ⇔ exists (svar zero ≈ svar (suc x) ∧ Ξ'))
    (sym (subst-inj-commute-ren (ren₀ x)))
    (cong
      inj-formula
      (trans
        (cong (λ φ → ren-formula (ren₀ zero) φ) (elim-extend-commute {Φ = Φ}))
        ren-zero-extend-ctx-id-formula))

Lemma'' : ∀ {Γ} {Φ : Formula₀ Γ} → Proof CT {𝟘} {Γ} Φ → Proof ST {𝟘} {Γ} (inj-formula (elim Φ))
Lemma'' {Φ = Φ} (axiom (set∈class C Γ y Ψ) σ r) =
  eq-to-⇔
    (cong
      inj-formula
      (trans
        (sym (elim-renamings-commute {Φ = Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Ψ)} (ren₀ (r y))))
        (cong
          elim
          (trans
            (ren₀-under-extend-Subst-Formula {Φ = ren-Formula (extend-ren r) Ψ} σ)
            (cong
              (λ Ξ → Subst-Formula σ Ξ)
              (ren₀-under-extend-ren r))))))
Lemma'' {Γ = Γ} (axiom class∈class σ r) with σ A | σ B 
Lemma'' {Γ = suc Γ} (axiom class∈class σ r) | svar x | svar y = axiom-exact (tmp _ _ x (svar zero ∈ svar (suc y)))
... | svar x  | class Φ =
  transport-proof
    (sym (weird-eq {Φ = Φ}))
    (axiom-exact (tmp _ _ x (inj-formula (elim Φ))))
... | class Φ | svar x =
  eq-to-⇔
    (cong
      (λ φ →
        exists
          (all (svar zero ∈ svar (suc zero) ⇔ inj-formula φ)
            ∧
          svar zero ∈ svar (suc x)))
      (sym (elim-extend-commute {Φ = Φ})))
... | class Φ | class Ψ =
  eq-to-⇔
    (cong₂
      (λ φ ψ →
        exists
          (all (svar zero ∈ svar (suc zero) ⇔ inj-formula φ)
            ∧
          inj-formula ψ))
      (sym (elim-extend-commute {Φ = Φ}))
      (sym (subst-extend-elim-eq {Φ = Ψ})))
Lemma'' (axiom class≈class σ r) with σ A | σ B 
... | svar x  | svar y = axiom-exact (ext _ x y)
... | svar x  | class Φ =
  eq-to-⇔
    (cong (λ φ → all (svar zero ∈ svar (suc x) ⇔ inj-formula φ))
    (sym (subst-extend-elim-eq {Φ = Φ})))
... | class Φ | svar x =
  eq-to-⇔
    (cong (λ φ → all (inj-formula φ ⇔ svar zero ∈ svar (suc x)))
    (sym (subst-extend-elim-eq {Φ = Φ})))
... | class Φ | class Ψ =
  eq-to-⇔
    (cong₂
      (λ φ ψ → all (inj-formula φ ⇔ inj-formula ψ))
      (sym (subst-extend-elim-eq {Φ = Φ}))
      (sym (subst-extend-elim-eq {Φ = Ψ})))
Lemma'' ⇔-refl = ⇔-refl
Lemma'' (∧-cong p p') = ∧-cong (Lemma'' p) (Lemma'' p')
Lemma'' (⇔-cong p p') = ⇔-cong (Lemma'' p) (Lemma'' p')
Lemma'' (¬-cong p) = ¬-cong (Lemma'' p)
Lemma'' (all-cong p) = all-cong (Lemma'' p)
Lemma'' (⇔-trans p p') = ⇔-trans (Lemma'' p) (Lemma'' p')
Lemma'' (exists-cong p) = exists-cong (Lemma'' p)
Lemma'' (axiom (tmp C Γ x Φ) σ r) = {!  !}

conservation-⇒'' : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
conservation-⇒'' φ p =
  transport-proof
    inj-elim-inj
    (Lemma''
      (transport-proof
        (inj-formula-Subst-id magic-Subst)
        (Subst-Proof magic-Subst p)))


-- The Conservation Theorem

conservation : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) ↔ Proof ST {𝟘} {Γ} (inj-formula φ)
conservation φ = conservation-⇒'' φ , conservation-⇐ φ