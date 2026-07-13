open import Data.Product

open import Syntax
open import Substitutions
open import Theory
open import Proof
open import Eliminability-Lemmas


eliminability-main-theorem : ∀ {Γ} (Φ : Formula₀ Γ) → Proof CT (Φ ⇔ (inj-formula (elim Φ)))
eliminability-main-theorem (svar x ≈ svar y) = ⇔-refl
eliminability-main-theorem {Γ = Γ} (svar x ≈ class Φ) = ⇔-trans lemma1 lemma7
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = svar x
    Subst-AB B = class Φ

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-Formula-ctx Φ

    lemma1 : Proof CT (svar x ≈ class Φ ⇔ all (svar zero ∈ svar (suc x) ⇔ svar zero ∈ class Φ+))
    lemma1 = axiom class≈class Subst-AB (λ ()) -- hack

    lemma2 : Proof CT ((svar zero ∈ svar (suc x) ⇔ svar zero ∈ class Φ+) ⇔ (svar zero ∈ svar (suc x) ⇔ Φ+ [ svar zero ]F))
    lemma2 = ⇔-cong ⇔-refl ⇔-∈-subst

    lemma3 : Proof CT ((svar zero ∈ svar (suc x) ⇔ Φ+ [ svar zero ]F) ⇔ (svar zero ∈ svar (suc x) ⇔ Φ))
    lemma3 = ⇔-cong ⇔-refl (eq-to-⇔ eq-subst-zero-Formula)

    lemma4 : Proof CT ((svar zero ∈ svar (suc x) ⇔ svar zero ∈ class Φ+) ⇔ (svar zero ∈ svar (suc x) ⇔ Φ))
    lemma4 = ⇔-trans lemma2 lemma3

    lemma5 : Proof CT ((svar zero ∈ svar (suc x) ⇔ Φ) ⇔ (svar zero ∈ svar (suc x) ⇔ inj-formula (elim Φ)))
    lemma5 = ⇔-cong ⇔-refl (eliminability-main-theorem Φ)

    lemma6 : Proof CT ((svar zero ∈ svar (suc x) ⇔ svar zero ∈ class Φ+) ⇔ (svar zero ∈ svar (suc x) ⇔ inj-formula (elim Φ)))
    lemma6 = ⇔-trans lemma4 lemma5

    lemma7 : Proof CT (all (svar zero ∈ svar (suc x) ⇔ svar zero ∈ class Φ+) ⇔ all (svar zero ∈ svar (suc x) ⇔ inj-formula (elim Φ)))
    lemma7 = all-cong lemma6
eliminability-main-theorem {Γ = Γ} (class Φ ≈ svar x) = ⇔-trans lemma1 lemma7
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = svar x

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-Formula-ctx Φ

    lemma1 : Proof CT (class Φ ≈ svar x ⇔ all (svar zero ∈ class Φ+ ⇔ svar zero ∈ svar (suc x)))
    lemma1 = axiom class≈class Subst-AB (λ ()) -- hack

    lemma2 : Proof CT ((svar zero ∈ class Φ+ ⇔ svar zero ∈ svar (suc x)) ⇔ (Φ+ [ svar zero ]F ⇔ svar zero ∈ svar (suc x)))
    lemma2 = ⇔-cong ⇔-∈-subst ⇔-refl

    lemma3 : Proof CT ((Φ+ [ svar zero ]F ⇔ svar zero ∈ svar (suc x)) ⇔ (Φ ⇔ svar zero ∈ svar (suc x)))
    lemma3 = ⇔-cong (eq-to-⇔ eq-subst-zero-Formula) ⇔-refl

    lemma4 : Proof CT ((svar zero ∈ class Φ+ ⇔ svar zero ∈ svar (suc x)) ⇔ (Φ ⇔ svar zero ∈ svar (suc x)))
    lemma4 = ⇔-trans lemma2 lemma3

    lemma5 : Proof CT ((Φ ⇔ svar zero ∈ svar (suc x)) ⇔ (inj-formula (elim Φ) ⇔ svar zero ∈ svar (suc x)))
    lemma5 = ⇔-cong (eliminability-main-theorem Φ) ⇔-refl

    lemma6 : Proof CT ((svar zero ∈ class Φ+ ⇔ svar zero ∈ svar (suc x)) ⇔ (inj-formula (elim Φ) ⇔ svar zero ∈ svar (suc x)))
    lemma6 = ⇔-trans lemma4 lemma5

    lemma7 : Proof CT (all (svar zero ∈ class Φ+ ⇔ svar zero ∈ svar (suc x)) ⇔ all (inj-formula (elim Φ) ⇔ svar zero ∈ svar (suc x)))
    lemma7 = all-cong lemma6
eliminability-main-theorem {Γ = Γ} (class Φ ≈ class Ψ) = ⇔-trans lemma1 lemma7
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = class Ψ

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-Formula-ctx Φ

    Ψ+ : Formula₀ (extend (extend Γ))
    Ψ+ = extend-Formula-ctx Ψ

    lemma1 : Proof CT (class Φ ≈ class Ψ ⇔ all (svar zero ∈ class Φ+ ⇔ svar zero ∈ class Ψ+))
    lemma1 = axiom class≈class Subst-AB (λ ()) -- hack

    lemma2 : Proof CT ((svar zero ∈ class Φ+ ⇔ svar zero ∈ class Ψ+) ⇔ (Φ+ [ svar zero ]F ⇔ Ψ+ [ svar zero ]F))
    lemma2 = ⇔-cong ⇔-∈-subst ⇔-∈-subst

    lemma3 : Proof CT ((Φ+ [ svar zero ]F ⇔ Ψ+ [ svar zero ]F) ⇔ (Φ ⇔ Ψ))
    lemma3 = ⇔-cong (eq-to-⇔ eq-subst-zero-Formula) (eq-to-⇔ eq-subst-zero-Formula)

    lemma4 : Proof CT ((svar zero ∈ class Φ+ ⇔ svar zero ∈ class Ψ+) ⇔ (Φ ⇔ Ψ))
    lemma4 = ⇔-trans lemma2 lemma3

    lemma5 : Proof CT ((Φ ⇔ Ψ) ⇔ (inj-formula (elim Φ) ⇔ inj-formula (elim Ψ)))
    lemma5 = ⇔-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)

    lemma6 : Proof CT ((svar zero ∈ class Φ+ ⇔ svar zero ∈ class Ψ+) ⇔ (inj-formula (elim Φ) ⇔ inj-formula (elim Ψ)))
    lemma6 = ⇔-trans lemma4 lemma5

    lemma7 : Proof CT (all (svar zero ∈ class Φ+ ⇔ svar zero ∈ class Ψ+) ⇔ all (inj-formula (elim Φ) ⇔ inj-formula (elim Ψ)))
    lemma7 = all-cong lemma6
eliminability-main-theorem (svar x ∈ svar y) = ⇔-refl
eliminability-main-theorem {Γ = Γ} (svar x ∈ class Φ) =
  ⇔-trans
    lemma
    (eq-to-⇔ (subst-inj-commute-ren-zero {φ = elim Φ}))
  where
    lemma : Proof CT (svar x ∈ class Φ ⇔ (inj-formula (elim Φ)) [ svar x ]F)
    lemma =
      ⇔-trans
        (axiom-exact (set∈class 𝟘 Γ x Φ))
        (subst-dist-⇔ x (eliminability-main-theorem Φ))
eliminability-main-theorem {Γ = Γ} (class Φ ∈ svar x) = ⇔-trans lemma1 lemma12
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = svar x

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-Formula-ctx Φ

    Φ++ : Formula₀ (extend (extend (extend Γ)))
    Φ++ = extend-Formula-ctx Φ+

    lemma1 : Proof CT (class Φ ∈ svar x ⇔ exists (svar zero ≈ class Φ+ ∧ svar zero ∈ svar (suc x)))
    lemma1 = axiom class∈class Subst-AB (λ ())

    lemma2 : Proof CT (svar zero ≈ class Φ+ ⇔ all (svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++))
    lemma2 = axiom class≈class (λ {A → svar zero ; B → class Φ+}) (λ ())

    lemma3 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ++ [ svar zero ]F)
    lemma3 = ⇔-∈-subst

    lemma4 : Proof CT (Φ++ [ svar zero ]F ⇔ Φ+)
    lemma4 = eq-to-⇔ eq-subst-zero-Formula

    lemma5 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ+)
    lemma5 = ⇔-trans lemma3 lemma4

    -- (ren-Formula (extend-ren suc) Φ)
    --  ⇔ inj-formula (elim (ren-Formula (extend-ren suc) Φ))
    --  ≡ ren-Formula (extend-ren suc) (inj-formula (elim Φ))
    lemma6 : Proof CT (Φ+ ⇔ inj-formula (elim Φ+))
    lemma6 = ≡-subst (λ Ξ → Proof CT (Φ+ ⇔ Ξ)) lemma6-2 lemma6-1
      where
        lemma6-1 : Proof CT (Φ+ ⇔ extend-Formula-ctx (inj-formula (elim Φ)))
        lemma6-1 = ren-Proof (extend-ren suc) (eliminability-main-theorem Φ)

        lemma6-2 : extend-Formula-ctx {C = 𝟘} (inj-formula (elim Φ)) ≡ inj-formula (elim Φ+)
        lemma6-2 =
          trans
            (subst-inj-commute-ren (extend-ren suc))
            (sym 
              (cong
                inj-formula
                (elim-renamings-commute {Φ = Φ} (extend-ren suc))))

    lemma7 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (elim Φ+))
    lemma7 = ⇔-trans lemma5 lemma6

    lemma8 : Proof CT (inj-formula (elim Φ+) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma8 = eq-to-⇔ (cong inj-formula (elim-extend-commute {Φ = Φ}))

    lemma9 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma9 = ⇔-trans lemma7 lemma8

    lemma10 :
      Proof CT
        ((svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++)
          ⇔
        (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma10 = ⇔-cong ⇔-refl lemma9

    lemma11 :
      Proof CT
        ((svar zero ≈ class Φ+)
          ⇔
        all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma11 = ⇔-trans lemma2 (all-cong lemma10)

    lemma12 :
      Proof CT
        ((exists (svar zero ≈ class Φ+ ∧ svar zero ∈ svar (suc x)))
          ⇔
        (exists (all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))) ∧ svar zero ∈ svar (suc x))))
    lemma12 = exists-cong (∧-cong lemma11 ⇔-refl)
eliminability-main-theorem {Γ = Γ} (class Φ ∈ class Ψ) = ⇔-trans lemma1 lemma12
  where
    Subst-AB : Subst Γ (thy-cls CT class≈class) 𝟘
    Subst-AB A = class Φ
    Subst-AB B = class Ψ

    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-Formula-ctx Φ

    Φ++ : Formula₀ (extend (extend (extend Γ)))
    Φ++ = extend-Formula-ctx Φ+

    Ψ+ : Formula₀ (extend (extend Γ))
    Ψ+ = extend-Formula-ctx Ψ

    lemma1 : Proof CT (class Φ ∈ class Ψ ⇔ exists (svar zero ≈ class Φ+ ∧ svar zero ∈ class Ψ+))
    lemma1 = axiom class∈class Subst-AB (λ ())

    lemma2 : Proof CT (svar zero ≈ class Φ+ ⇔ all (svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++))
    lemma2 = axiom class≈class (λ {A → svar zero ; B → class Φ+}) (λ ())

    lemma3 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ++ [ svar zero ]F)
    lemma3 = ⇔-∈-subst

    lemma4 : Proof CT (Φ++ [ svar zero ]F ⇔ Φ+)
    lemma4 = eq-to-⇔ eq-subst-zero-Formula

    lemma5 : Proof CT ((svar zero ∈ class Φ++) ⇔ Φ+)
    lemma5 = ⇔-trans lemma3 lemma4

    -- (ren-Formula (extend-ren suc) Φ)
    --  ⇔ inj-formula (elim (ren-Formula (extend-ren suc) Φ))
    --  ≡ ren-Formula (extend-ren suc) (inj-formula (elim Φ))
    lemma6 : Proof CT (Φ+ ⇔ inj-formula (elim Φ+))
    lemma6 = ≡-subst (λ Ξ → Proof CT (Φ+ ⇔ Ξ)) lemma6-2 lemma6-1
      where
        lemma6-1 : Proof CT (Φ+ ⇔ extend-Formula-ctx (inj-formula (elim Φ)))
        lemma6-1 = ren-Proof (extend-ren suc) (eliminability-main-theorem Φ)

        lemma6-2 : extend-Formula-ctx {C = 𝟘} (inj-formula (elim Φ)) ≡ inj-formula (elim Φ+)
        lemma6-2 =
          trans
            (subst-inj-commute-ren (extend-ren suc))
            (sym 
              (cong
                inj-formula
                (elim-renamings-commute {Φ = Φ} (extend-ren suc))))

    lemma7 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (elim Φ+))
    lemma7 = ⇔-trans lemma5 lemma6

    lemma8 : Proof CT (inj-formula (elim Φ+) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma8 = eq-to-⇔ (cong inj-formula (elim-extend-commute {Φ = Φ}))

    lemma9 : Proof CT ((svar zero ∈ class Φ++) ⇔ inj-formula (extend-formula-ctx (elim Φ)))
    lemma9 = ⇔-trans lemma7 lemma8

    lemma10 :
      Proof CT
        ((svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++)
          ⇔
        (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma10 = ⇔-cong ⇔-refl lemma9

    lemma11 :
      Proof CT
        ((svar zero ≈ class Φ+)
          ⇔
        all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))))
    lemma11 = ⇔-trans lemma2 (all-cong lemma10)

    lemma12 :
      Proof CT
        ((exists (svar zero ≈ class Φ+ ∧ svar zero ∈ class Ψ+))
          ⇔
        (exists (all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-formula-ctx (elim Φ))) ∧ inj-formula (elim Ψ))))
    lemma12 = exists-cong (∧-cong lemma11 lemma12-1)
     where
      lemma12-1 : Proof CT (svar zero ∈ class Ψ+ ⇔ inj-formula (elim Ψ))
      lemma12-1 =
        ⇔-trans
          (⇔-trans
            ⇔-∈-subst
            (eq-to-⇔ eq-subst-zero-Formula))
          (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ∧ Ψ) = ∧-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ⇔ Ψ) = ⇔-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (¬ Φ) = ¬-cong (eliminability-main-theorem Φ)
eliminability-main-theorem (all Φ) = all-cong (eliminability-main-theorem Φ)
eliminability-main-theorem (exists Φ) = exists-cong (eliminability-main-theorem Φ)


-- The Eliminability Theorem

eliminability : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → Proof CT (Subst-Formula σ Φ ⇔ inj-formula (elim (Subst-Formula σ Φ)))
eliminability C Φ σ  = eliminability-main-theorem (Subst-Formula σ Φ)

existential-eliminability : ∀ C {Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) → ∃[ φ ] Proof CT (Subst-Formula σ Φ ⇔ inj-formula φ)
existential-eliminability C Φ σ = elim (Subst-Formula σ Φ) , eliminability C Φ σ