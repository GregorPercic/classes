open import Syntax
open import Substitutions


record Theory : Set₂ where
  field
    thy-idx : Set₁ -- axiom names
    thy-cls : thy-idx → Set -- class variables appearing in the axiom
    thy-ctx : thy-idx → Ctx -- set variables appearing in the axiom
    thy-axi : (i : thy-idx) → Formula (thy-cls i) (thy-ctx i)

open Theory public


-- The theory of classes

data idxCT : Set₁ where
  -- the axiom schema y ∈ {x | Φ} ⇔ Φ[y/x]
  set∈class : (C : Set) (Γ : Ctx) (y : Var Γ) (Φ : Formula C (extend Γ)) → idxCT
  -- the axiom A ∈ B ⇔ ∃x.(x = A ∧ x ∈ B)
  class∈class : idxCT
  -- the axiom A = B ⇔ ∀x.(x ∈ A ⇔ x ∈ B)
  class≈class : idxCT

data two-classes : Set where
  A B : two-classes

CT : Theory
thy-idx CT = idxCT

thy-cls CT (set∈class C Γ y Φ) = C
thy-cls CT class∈class = two-classes
thy-cls CT class≈class = two-classes

thy-ctx CT (set∈class C Γ y Φ) = Γ
thy-ctx CT class∈class = ⟨⟩
thy-ctx CT class≈class = ⟨⟩

thy-axi CT (set∈class C Γ y Φ) = svar y ∈ class Φ ⇔ Φ [ svar y ]F
thy-axi CT class∈class = cvar A ∈ cvar B ⇔ exists (svar zero ≈ cvar A ∧ svar zero ∈ cvar B)
thy-axi CT class≈class = cvar A ≈ cvar B ⇔ all (svar zero ∈ cvar A ⇔ svar zero ∈ cvar B)