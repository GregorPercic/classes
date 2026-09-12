open import Data.Product using (∃-syntax ; _,_)

open import TTheory
open import PProof
open import Eliminability-Lemmas


eliminability-main-theorem : ∀ {Γ} (Φ : Formula₀ Γ) → Proof CT [] (Φ ⇔ (inj-formula (elim Φ)))
eliminability-main-theorem ⊥ = ⇔-refl
eliminability-main-theorem (svar x ≈ svar y) = ⇔-refl
eliminability-main-theorem {Γ = Γ} (svar x ≈ class Φ) = ⇔-all-cong-Proof ⇔-refl ⇔-refl lemma2 lemma1
  where
    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-ren-suc-Formula Φ

    lemma1 : Proof CT [] (svar x ≈ class Φ ⇔ all (svar zero ∈ svar (suc x) ⇔ svar zero ∈ class Φ+))
    lemma1 = axiom class≈class (λ {A → svar x ; B → class Φ}) empty-ren

    lemma2 : Proof CT [] (svar zero ∈ class Φ+ ⇔ inj-formula (elim Φ))
    lemma2 =
      ⇔-trans
        (⇔-trans
          ⇔-∈-subst
          (eq-to-⇔ subst-zero-eq-Formula))
        (eliminability-main-theorem Φ)
eliminability-main-theorem {Γ = Γ} (class Φ ≈ svar x) = ⇔-all-cong-Proof ⇔-refl lemma2 ⇔-refl lemma1
  where
    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-ren-suc-Formula Φ

    lemma1 : Proof CT [] (class Φ ≈ svar x ⇔ all (svar zero ∈ class Φ+ ⇔ svar zero ∈ svar (suc x)))
    lemma1 = axiom class≈class (λ {A → class Φ ; B → svar x}) empty-ren

    lemma2 : Proof CT [] (svar zero ∈ class Φ+ ⇔ inj-formula (elim Φ))
    lemma2 =
      ⇔-trans
        (⇔-trans
          ⇔-∈-subst
          (eq-to-⇔ subst-zero-eq-Formula))
        (eliminability-main-theorem Φ)
eliminability-main-theorem {Γ = Γ} (class Φ ≈ class Ψ) = ⇔-all-cong-Proof ⇔-refl lemma2 lemma3 lemma1
  where
    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-ren-suc-Formula Φ

    Ψ+ : Formula₀ (extend (extend Γ))
    Ψ+ = extend-ren-suc-Formula Ψ

    lemma1 : Proof CT [] (class Φ ≈ class Ψ ⇔ all (svar zero ∈ class Φ+ ⇔ svar zero ∈ class Ψ+))
    lemma1 = axiom class≈class (λ {A → class Φ ; B → class Ψ}) empty-ren

    lemma2 : Proof CT [] (svar zero ∈ class Φ+ ⇔ inj-formula (elim Φ))
    lemma2 =
      ⇔-trans
        (⇔-trans
          ⇔-∈-subst
          (eq-to-⇔ subst-zero-eq-Formula))
        (eliminability-main-theorem Φ)
    
    lemma3 : Proof CT [] (svar zero ∈ class Ψ+ ⇔ inj-formula (elim Ψ))
    lemma3 =
      ⇔-trans
        (⇔-trans
          ⇔-∈-subst
          (eq-to-⇔ subst-zero-eq-Formula))
        (eliminability-main-theorem Ψ)
eliminability-main-theorem (svar x ∈ svar y) = ⇔-refl
eliminability-main-theorem {Γ = Γ} (svar x ∈ class Φ) =
  ⇔-trans
    lemma
    (eq-to-⇔ (ren₀-inj-formula {φ = elim Φ}))
  where
    lemma : Proof CT [] (svar x ∈ class Φ ⇔ (inj-formula (elim Φ)) [ svar x ]F)
    lemma =
      ⇔-trans
        (axiom-exact (set∈class 𝟘 Γ x Φ))
        (subst-dist-⇔ x (eliminability-main-theorem Φ))
eliminability-main-theorem {Γ = Γ} (class Φ ∈ svar x) = ⇔-trans lemma1 lemma12
  where
    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-ren-suc-Formula Φ

    Φ++ : Formula₀ (extend (extend (extend Γ)))
    Φ++ = extend-ren-suc-Formula Φ+

    lemma1 : Proof CT [] (class Φ ∈ svar x ⇔ exists (svar zero ≈ class Φ+ ∧ svar zero ∈ svar (suc x)))
    lemma1 = axiom class∈class (λ {A → class Φ ; B → svar x}) empty-ren

    lemma2 : Proof CT [] (svar zero ≈ class Φ+ ⇔ all (svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++))
    lemma2 = axiom class≈class (λ {A → svar zero ; B → class Φ+}) empty-ren

    lemma3 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ Φ++ [ svar zero ]F)
    lemma3 = ⇔-∈-subst

    lemma4 : Proof CT [] (Φ++ [ svar zero ]F ⇔ Φ+)
    lemma4 = eq-to-⇔ subst-zero-eq-Formula

    lemma5 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ Φ+)
    lemma5 = ⇔-trans lemma3 lemma4

    -- (ren-Formula (extend-ren suc) Φ)
    --  ⇔ inj-formula (elim (ren-Formula (extend-ren suc) Φ))
    --  ≡ ren-Formula (extend-ren suc) (inj-formula (elim Φ))
    lemma6 : Proof CT [] (Φ+ ⇔ inj-formula (elim Φ+))
    lemma6 = ≡-subst (λ Ξ → Proof CT [] (Φ+ ⇔ Ξ)) lemma6-2 lemma6-1
      where
        lemma6-1 : Proof CT [] (Φ+ ⇔ extend-ren-suc-Formula (inj-formula (elim Φ)))
        lemma6-1 = ren-Proof (extend-ren suc) (eliminability-main-theorem Φ)

        lemma6-2 : extend-ren-suc-Formula {C = 𝟘} (inj-formula (elim Φ)) ≡ inj-formula (elim Φ+)
        lemma6-2 =
          trans
            (ren-inj-formula (extend-ren suc))
            (sym
              (cong
                inj-formula
                (elim-ren {Φ = Φ} (extend-ren suc))))

    lemma7 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ inj-formula (elim Φ+))
    lemma7 = ⇔-trans lemma5 lemma6

    lemma8 : Proof CT [] (inj-formula (elim Φ+) ⇔ inj-formula (extend-ren-suc-formula (elim Φ)))
    lemma8 = eq-to-⇔ (cong inj-formula (elim-extend-suc {Φ = Φ}))

    lemma9 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ inj-formula (extend-ren-suc-formula (elim Φ)))
    lemma9 = ⇔-trans lemma7 lemma8

    lemma10 :
      Proof CT []
        ((svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++)
          ⇔
        (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-ren-suc-formula (elim Φ))))
    lemma10 = ⇔-cong ⇔-refl lemma9

    lemma11 :
      Proof CT []
        ((svar zero ≈ class Φ+)
          ⇔
        all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-ren-suc-formula (elim Φ))))
    lemma11 = ⇔-trans lemma2 (all-cong lemma10)

    lemma12 :
      Proof CT []
        ((exists (svar zero ≈ class Φ+ ∧ svar zero ∈ svar (suc x)))
          ⇔
        (exists (all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-ren-suc-formula (elim Φ))) ∧ svar zero ∈ svar (suc x))))
    lemma12 = exists-cong (∧-cong lemma11 ⇔-refl)
eliminability-main-theorem {Γ = Γ} (class Φ ∈ class Ψ) = ⇔-trans lemma1 lemma12
  where
    Φ+ : Formula₀ (extend (extend Γ))
    Φ+ = extend-ren-suc-Formula Φ

    Φ++ : Formula₀ (extend (extend (extend Γ)))
    Φ++ = extend-ren-suc-Formula Φ+

    Ψ+ : Formula₀ (extend (extend Γ))
    Ψ+ = extend-ren-suc-Formula Ψ

    lemma1 : Proof CT [] (class Φ ∈ class Ψ ⇔ exists (svar zero ≈ class Φ+ ∧ svar zero ∈ class Ψ+))
    lemma1 = axiom class∈class (λ {A → class Φ ; B → class Ψ}) empty-ren

    lemma2 : Proof CT [] (svar zero ≈ class Φ+ ⇔ all (svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++))
    lemma2 = axiom class≈class (λ {A → svar zero ; B → class Φ+}) empty-ren

    lemma3 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ Φ++ [ svar zero ]F)
    lemma3 = ⇔-∈-subst

    lemma4 : Proof CT [] (Φ++ [ svar zero ]F ⇔ Φ+)
    lemma4 = eq-to-⇔ subst-zero-eq-Formula

    lemma5 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ Φ+)
    lemma5 = ⇔-trans lemma3 lemma4

    -- (ren-Formula (extend-ren suc) Φ)
    --  ⇔ inj-formula (elim (ren-Formula (extend-ren suc) Φ))
    --  ≡ ren-Formula (extend-ren suc) (inj-formula (elim Φ))
    lemma6 : Proof CT [] (Φ+ ⇔ inj-formula (elim Φ+))
    lemma6 = ≡-subst (λ Ξ → Proof CT [] (Φ+ ⇔ Ξ)) lemma6-2 lemma6-1
      where
        lemma6-1 : Proof CT [] (Φ+ ⇔ extend-ren-suc-Formula (inj-formula (elim Φ)))
        lemma6-1 = ren-Proof (extend-ren suc) (eliminability-main-theorem Φ)

        lemma6-2 : extend-ren-suc-Formula {C = 𝟘} (inj-formula (elim Φ)) ≡ inj-formula (elim Φ+)
        lemma6-2 =
          trans
            (ren-inj-formula (extend-ren suc))
            (sym 
              (cong
                inj-formula
                (elim-ren {Φ = Φ} (extend-ren suc))))

    lemma7 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ inj-formula (elim Φ+))
    lemma7 = ⇔-trans lemma5 lemma6

    lemma8 : Proof CT [] (inj-formula (elim Φ+) ⇔ inj-formula (extend-ren-suc-formula (elim Φ)))
    lemma8 = eq-to-⇔ (cong inj-formula (elim-extend-suc {Φ = Φ}))

    lemma9 : Proof CT [] ((svar zero ∈ class Φ++) ⇔ inj-formula (extend-ren-suc-formula (elim Φ)))
    lemma9 = ⇔-trans lemma7 lemma8

    lemma10 :
      Proof CT []
        ((svar zero ∈ svar (suc zero) ⇔ svar zero ∈ class Φ++)
          ⇔
        (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-ren-suc-formula (elim Φ))))
    lemma10 = ⇔-cong ⇔-refl lemma9

    lemma11 :
      Proof CT []
        ((svar zero ≈ class Φ+)
          ⇔
        all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-ren-suc-formula (elim Φ))))
    lemma11 = ⇔-trans lemma2 (all-cong lemma10)

    lemma12 :
      Proof CT []
        ((exists (svar zero ≈ class Φ+ ∧ svar zero ∈ class Ψ+))
          ⇔
        (exists (all (svar zero ∈ svar (suc zero) ⇔ inj-formula (extend-ren-suc-formula (elim Φ))) ∧ inj-formula (elim Ψ))))
    lemma12 = exists-cong (∧-cong lemma11 lemma12-1)
      where
        lemma12-1 : Proof CT [] (svar zero ∈ class Ψ+ ⇔ inj-formula (elim Ψ))
        lemma12-1 =
          ⇔-trans
            (⇔-trans
              ⇔-∈-subst
              (eq-to-⇔ subst-zero-eq-Formula))
            (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ∧ Ψ) = ∧-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ⇒ Ψ) = ⇒-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (Φ ⇔ Ψ) = ⇔-cong (eliminability-main-theorem Φ) (eliminability-main-theorem Ψ)
eliminability-main-theorem (all Φ) = all-cong (eliminability-main-theorem Φ)
eliminability-main-theorem (exists Φ) = exists-cong (eliminability-main-theorem Φ)


-- The Eliminability Theorem

eliminability : ∀ {C Γ} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) →
  Proof CT {𝟘} {Γ} [] (Subst-Formula σ Φ ⇔ inj-formula (elim (Subst-Formula σ Φ)))
eliminability Φ σ  = eliminability-main-theorem (Subst-Formula σ Φ)

eliminability-Hyp : ∀ {C Γ Hyp} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) →
  Proof CT {𝟘} {Γ} Hyp (Subst-Formula σ Φ ⇔ inj-formula (elim (Subst-Formula σ Φ)))
eliminability-Hyp Φ σ = wk-from-empty (eliminability Φ σ)

existential-eliminability : ∀ {C Γ Hyp} (Φ : Formula C Γ) (σ : Subst Γ C 𝟘) →
  ∃[ φ ] Proof CT {𝟘} {Γ} Hyp (Subst-Formula σ Φ ⇔ inj-formula φ)
existential-eliminability Φ σ = elim (Subst-Formula σ Φ) , eliminability-Hyp Φ σ