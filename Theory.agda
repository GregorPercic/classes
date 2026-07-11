open import Syntax
open import Substitutions


record Theory : Set₁ where
  field
    thy-idx : Set -- axiom names
    thy-cls : thy-idx → Set -- class variables appearing in the axiom
    thy-ctx : thy-idx → Ctx -- set variables appearing in the axiom
    thy-axi : ∀ (i : thy-idx) → Formula (thy-cls i) (thy-ctx i)

open Theory public


-- The theory of classes

data idxCT : Set where
  -- the axiom schema y ∈ { x | Φ } ⇔ Φ[y/x]
  set∈class : (n : ℕ) (Γ : Ctx) (y : Var Γ) (Φ : Formula (Fin-with-𝟘 n) (extend Γ)) → idxCT
  -- the axiom A ∈ B ⇔ ∃x.(x = A ∧ x ∈ B)
  class∈class : idxCT
  -- the axiom A = B ⇔ ∀x.(x ∈ A ⇔ x ∈ B)
  class≈class : idxCT

data twoClasses : Set where
  A B : twoClasses

CT : Theory
thy-idx CT = idxCT

thy-cls CT (set∈class n Γ y Φ) = Fin-with-𝟘 n
thy-cls CT class∈class = twoClasses
thy-cls CT class≈class = twoClasses

thy-ctx CT (set∈class n Γ y Φ) = Γ
thy-ctx CT class∈class = ⟨⟩
thy-ctx CT class≈class = ⟨⟩

thy-axi CT (set∈class n Γ y Φ) = svar y ∈ class Φ ⇔ Φ [ svar y ]F
thy-axi CT class∈class = cvar A ∈ cvar B ⇔ exists (svar zero ≈ cvar A ∧ svar zero ∈ cvar B)
thy-axi CT class≈class = cvar A ≈ cvar B ⇔ all (svar zero ∈ cvar A ⇔ svar zero ∈ cvar B)


-- The basic first-order set theory with Extensionality as its only axiom

data idxST : Set where
  ext : idxST

ST : Theory
thy-idx ST = idxST

thy-cls ST ext = 𝟘

thy-ctx ST ext = ⟨⟩
-- the axiom of extensionality: ∀x∀y.(x = y ⇔ ∀z.(z ∈ x ⇔ z ∈ y))
thy-axi ST ext = all (all (svar (suc zero) ≈ svar zero ⇔ all (svar zero ∈ svar (suc (suc zero)) ⇔ svar zero ∈ svar (suc zero))))
