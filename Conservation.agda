open import Data.Product hiding (map)

open import Syntax
open import Substitutions
open import Proof
open import PProof
open import Theory
open import TTheory
open import Eliminability

open import Agda.Primitive


_↔_ : ∀ {ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
ty ↔ ty' = (ty → ty') × (ty' → ty)

inj-formula-l : ∀ {C Γ} → List (formula Γ) → List (Formula C Γ)
inj-formula-l = map inj-formula

inj-list-mem : ∀ {C Γ hyp} {φ : formula Γ} → hyp ∋ φ → map (inj-formula {C = C}) hyp ∋ inj-formula φ
inj-list-mem {φ = φ} here = here
inj-list-mem {φ = φ} (there is-in) = there (inj-list-mem is-in)

inj-formula-l-lemma : ∀ {C Γ} {hyp : List (formula Γ)} → inj-formula-l {C = C} (Proof.weaken-l hyp) ≡ PProof.weaken-l (inj-formula-l hyp)
inj-formula-l-lemma {hyp = []} = refl
inj-formula-l-lemma {hyp = φ ∷l hyp} = cong₂ _∷l_ (sym (subst-inj-commute-ren suc)) inj-formula-l-lemma

inj-formula-term-subst : ∀ {C Γ} {t : term Γ} {φ : formula (extend Γ)} → inj-formula {C = C} (φ [ t ]f) ≡ (inj-formula φ [ t ]F)
inj-formula-term-subst {t = svar x} = sym (subst-inj-commute-ren (ren₀ x))

conservation-⇐ : ∀ {C Γ hyp} {φ : formula Γ} → proof ST hyp φ → Proof CT {C = C} (inj-formula-l hyp) (inj-formula φ)
conservation-⇐ (axiom (ext Γ x y) r) = axiom class≈class (λ {A → svar (r x) ; B → svar (r y)}) empty-ren
conservation-⇐ (hyp-ax is-in) = Hyp-ax (inj-list-mem is-in)
conservation-⇐ ≈-refl = ≈-refl
conservation-⇐ (∧-i p p') = ∧-i (conservation-⇐ p) (conservation-⇐ p')
conservation-⇐ (⇒-i p) = ⇒-i (conservation-⇐ p)
conservation-⇐ (⇔-i p p') = ⇔-i (conservation-⇐ p) (conservation-⇐ p')
conservation-⇐ (all-i p) = all-i (transport-Proof-Hyp inj-formula-l-lemma (conservation-⇐ p))
conservation-⇐ (exists-i t p) = exists-i t (transport-Proof (inj-formula-term-subst {t = t}) (conservation-⇐ p))
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
        (sym (subst-inj-commute-ren suc))
        (conservation-⇐ p')))
conservation-⇐ (all-e t p) = transport-Proof (sym (inj-formula-term-subst {t = t})) (all-e t (conservation-⇐ p))
conservation-⇐ (≈-e {t = t} {u = u} p p') =
  transport-Proof
    (sym (inj-formula-term-subst {t = u}))
    (≈-e
      (conservation-⇐ p)
      (transport-Proof
        (inj-formula-term-subst {t = t})
        (conservation-⇐ p')))

conservation-⇒-lemma : ∀ {Γ Hyp} {Φ : Formula₀ Γ} → Proof CT {𝟘} {Γ} Hyp Φ → proof ST {Γ} (map elim Hyp) (elim Φ)
conservation-⇒-lemma p = {!  !}

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

elim-inj-inv : ∀ {Γ} {φ : formula Γ} → elim (inj-formula φ) ≡ φ
elim-inj-inv {φ = ⊥} = refl
elim-inj-inv {φ = svar x ≈ svar y} = refl
elim-inj-inv {φ = svar x ∈ svar y} = refl
elim-inj-inv {φ = φ ∧ ψ} = cong₂ _∧_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = φ ⇒ ψ} = cong₂ _⇒_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = φ ⇔ ψ} = cong₂ _⇔_ elim-inj-inv elim-inj-inv
elim-inj-inv {φ = all φ} = cong all elim-inj-inv
elim-inj-inv {φ = exists φ} = cong exists elim-inj-inv

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

conservation : ∀ {C Γ hyp} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula-l hyp) (inj-formula φ) ↔ proof ST {Γ} hyp φ
conservation φ = conservation-⇒ , conservation-⇐

conservation-corollary : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} [] (inj-formula φ) ↔ proof ST {Γ} [] φ
conservation-corollary φ = conservation φ

-- conservation-⇐-lemma : ∀ {Γ} {Φ : Formula₀ Γ} → Proof ST {𝟘} {Γ} Φ → Proof CT {𝟘} {Γ} Φ
-- conservation-⇐-lemma (axiom (ext Γ x y) σ r) =
--   Subst-Proof σ (ren-Proof r (axiom class≈class (λ {A → svar x ; B → svar y}) empty-ren))
-- conservation-⇐-lemma (axiom (in-equiv Γ x y) σ r) =
--   Subst-Proof σ (ren-Proof r (axiom class∈class (λ {A → svar x ; B → svar y}) empty-ren))
-- conservation-⇐-lemma ⇔-refl = ⇔-refl
-- conservation-⇐-lemma (∧-cong p p') = ∧-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
-- conservation-⇐-lemma (⇔-cong p p') = ⇔-cong (conservation-⇐-lemma p) (conservation-⇐-lemma p')
-- conservation-⇐-lemma (¬-cong p) = ¬-cong (conservation-⇐-lemma p)
-- conservation-⇐-lemma (all-cong p) = all-cong (conservation-⇐-lemma p)
-- conservation-⇐-lemma (⇔-trans p p') = ⇔-trans (conservation-⇐-lemma p) (conservation-⇐-lemma p')
-- conservation-⇐-lemma (exists-cong p) = exists-cong (conservation-⇐-lemma p)
-- conservation-⇐-lemma (axiom (tmp C Γ x Φ) σ r) = axiom (tmp C Γ x Φ) σ r
-- 
-- conservation-⇐ : ∀ {C Γ} (φ : formula Γ) → Proof ST {𝟘} {Γ} (inj-formula φ) → Proof CT {C} {Γ} (inj-formula φ)
-- conservation-⇐ φ p =
--   transport-Proof
--     Subst-empty-id
--     (Subst-Proof empty-Subst (conservation-⇐-lemma {Φ = inj-formula φ} p))
-- 
-- -- svar-injective : ∀ {C Γ} {x y : Var Γ} → Term.svar {C = C} x ≡ svar y → x ≡ y
-- -- svar-injective refl = refl
-- 
-- 
-- 
-- inj-elim-inj : ∀ {C Γ} {φ : formula Γ} → inj-formula {C = C} (elim (inj-formula φ)) ≡ inj-formula φ
-- inj-elim-inj = cong inj-formula elim-inj-inv
-- 
-- subst-extend-elim-eq : ∀ {Γ} {Φ : Formula₀ (extend Γ)} → ren-formula (ren₀ zero) (elim (ren-Formula (extend-ren suc) Φ)) ≡ elim Φ
-- subst-extend-elim-eq {Φ = Φ} =
--   trans
--     (sym (elim-renamings-commute {Φ = ren-Formula (extend-ren suc) Φ} (ren₀ zero)))
--     (trans
--       (cong elim (ren-comp-Formula {Φ = Φ} (extend-ren suc) (ren₀ zero)))
--       (trans
--         (cong (λ r → elim (ren-Formula r Φ)) ren-zero-extend-ctx-id)
--         (cong elim (id-ren-Formula {Φ = Φ}))))
-- 
-- 
-- weird-eq : ∀ {C : Set} {Γ} {x : Var Γ} {Φ : Formula₀ (extend Γ)} →
--   _≡_ {a = lzero} {A = Formula C Γ}
--     (inj-formula (ren-formula (ren₀ x) (elim Φ))
--       ⇔
--     exists (svar zero ≈ svar (suc x) ∧ inj-formula (ren-formula (ren₀ zero) (elim (ren-Formula (extend-ren suc) Φ)))))
--     (ren-Formula (ren₀ x) (inj-formula (elim Φ))
--       ⇔
--     exists (svar zero ≈ svar (suc x) ∧ inj-formula (elim Φ)))
-- weird-eq {x = x} {Φ = Φ} =
--   cong₂
--     (λ Ξ Ξ' → Ξ ⇔ exists (svar zero ≈ svar (suc x) ∧ Ξ'))
--     (sym (subst-inj-commute-ren (ren₀ x)))
--     (cong
--       inj-formula
--       (trans
--         (cong (λ φ → ren-formula (ren₀ zero) φ) (elim-extend-commute {Φ = Φ}))
--         ren-zero-extend-ctx-id-formula))
-- 
-- Lemma'' : ∀ {Γ} {Φ : Formula₀ Γ} → Proof CT {𝟘} {Γ} Φ → Proof ST {𝟘} {Γ} (inj-formula (elim Φ))
-- Lemma'' {Φ = Φ} (axiom (set∈class C Γ y Ψ) σ r) =
--   eq-to-⇔
--     (cong
--       inj-formula
--       (trans
--         (sym (elim-renamings-commute {Φ = Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Ψ)} (ren₀ (r y))))
--         (cong
--           elim
--           (trans
--             (ren₀-under-extend-Subst-Formula {Φ = ren-Formula (extend-ren r) Ψ} σ)
--             (cong
--               (λ Ξ → Subst-Formula σ Ξ)
--               (ren₀-under-extend-ren r))))))
-- Lemma'' {Γ = Γ} (axiom class∈class σ r) with σ A | σ B 
-- Lemma'' {Γ = suc Γ} (axiom class∈class σ r) | svar x | svar y = axiom-exact (tmp _ _ x (svar zero ∈ svar (suc y)))
-- ... | svar x  | class Φ =
--   transport-Proof
--     (sym (weird-eq {Φ = Φ}))
--     (axiom-exact (tmp _ _ x (inj-formula (elim Φ))))
-- ... | class Φ | svar x =
--   eq-to-⇔
--     (cong
--       (λ φ →
--         exists
--           (all (svar zero ∈ svar (suc zero) ⇔ inj-formula φ)
--             ∧
--           svar zero ∈ svar (suc x)))
--       (sym (elim-extend-commute {Φ = Φ})))
-- ... | class Φ | class Ψ =
--   eq-to-⇔
--     (cong₂
--       (λ φ ψ →
--         exists
--           (all (svar zero ∈ svar (suc zero) ⇔ inj-formula φ)
--             ∧
--           inj-formula ψ))
--       (sym (elim-extend-commute {Φ = Φ}))
--       (sym (subst-extend-elim-eq {Φ = Ψ})))
-- Lemma'' (axiom class≈class σ r) with σ A | σ B 
-- ... | svar x  | svar y = axiom-exact (ext _ x y)
-- ... | svar x  | class Φ =
--   eq-to-⇔
--     (cong (λ φ → all (svar zero ∈ svar (suc x) ⇔ inj-formula φ))
--     (sym (subst-extend-elim-eq {Φ = Φ})))
-- ... | class Φ | svar x =
--   eq-to-⇔
--     (cong (λ φ → all (inj-formula φ ⇔ svar zero ∈ svar (suc x)))
--     (sym (subst-extend-elim-eq {Φ = Φ})))
-- ... | class Φ | class Ψ =
--   eq-to-⇔
--     (cong₂
--       (λ φ ψ → all (inj-formula φ ⇔ inj-formula ψ))
--       (sym (subst-extend-elim-eq {Φ = Φ}))
--       (sym (subst-extend-elim-eq {Φ = Ψ})))
-- Lemma'' ⇔-refl = ⇔-refl
-- Lemma'' (∧-cong p p') = ∧-cong (Lemma'' p) (Lemma'' p')
-- Lemma'' (⇔-cong p p') = ⇔-cong (Lemma'' p) (Lemma'' p')
-- Lemma'' (¬-cong p) = ¬-cong (Lemma'' p)
-- Lemma'' (all-cong p) = all-cong (Lemma'' p)
-- Lemma'' (⇔-trans p p') = ⇔-trans (Lemma'' p) (Lemma'' p')
-- Lemma'' (exists-cong p) = exists-cong (Lemma'' p)
-- Lemma'' (axiom (tmp C Γ x Φ) σ r) =
--   transport-Proof
--     (sym weird-eq-tmp)
--     (axiom-exact (tmp _ _ (r x) _))
--   where
--     weird-eq-tmp :
--       _≡_ {a = lzero} {A = Formula₀ _}
--         (inj-formula (elim (Subst-Formula σ (ren-Formula r (ren-Formula (ren₀ x) Φ))))
--           ⇔
--         exists (svar zero ≈ svar (suc (r x)) ∧
--         inj-formula (elim (Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)))))
--         
--         (ren-Formula (ren₀ (r x)) (inj-formula (elim (Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ))))
--           ⇔
--         exists (svar zero ≈ svar (suc (r x)) ∧
--         inj-formula (elim (Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)))))
--     weird-eq-tmp =
--       cong
--         (λ Ξ → Ξ ⇔ exists (svar zero ≈ svar (suc (r x)) ∧ inj-formula (elim (Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)))))
--         (sym
--           (trans
--             (subst-inj-commute-ren (ren₀ (r x)))
--             (trans
--               (cong
--                 (λ φ → inj-formula φ)
--                 (sym
--                   (elim-renamings-commute
--                     {Φ = Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ)}
--                     (ren₀ (r x)))))
--               (cong
--                 (λ Ξ → inj-formula (elim Ξ))
--                 lemma))))
--                   where
--                     lemma :
--                       ren-Formula (ren₀ (r x)) (Subst-Formula (extend-Subst σ) (ren-Formula (extend-ren r) Φ))
--                         ≡
--                       Subst-Formula σ (ren-Formula r (ren-Formula (ren₀ x) Φ))
--                     lemma =
--                       trans
--                         (ren₀-under-extend-Subst-Formula σ)
--                         (cong
--                           (λ Ξ → Subst-Formula σ Ξ)
--                           (ren₀-under-extend-ren r))
-- 
-- 
-- conservation-⇒'' : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) → Proof ST {𝟘} {Γ} (inj-formula φ)
-- conservation-⇒'' φ p =
--   transport-Proof
--     inj-elim-inj
--     (Lemma''
--       (transport-Proof
--         (inj-formula-Subst-id magic-Subst)
--         (Subst-Proof magic-Subst p)))
-- 
-- 
-- -- The Conservation Theorem
-- 
-- conservation : ∀ {C Γ} (φ : formula Γ) → Proof CT {C} {Γ} (inj-formula φ) ↔ Proof ST {𝟘} {Γ} (inj-formula φ)
-- conservation φ = conservation-⇒'' φ , conservation-⇐ φ