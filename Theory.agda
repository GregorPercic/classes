open import Syntax
open import Substitutions


record Theory : Set₂ where
  field
    thy-idx : Set₁ -- axiom names
    thy-cls : thy-idx → Set -- class variables appearing in the axiom
    thy-ctx : thy-idx → Ctx -- set variables appearing in the axiom
    thy-axi : ∀ (i : thy-idx) → Formula (thy-cls i) (thy-ctx i)

open Theory public


-- The theory of classes

data idxCT : Set₁ where
  -- the axiom schema y ∈ { x | Φ } ⇔ Φ[y/x]
  set∈class : (C : Set) (Γ : Ctx) (y : Var Γ) (Φ : Formula C (extend Γ)) → idxCT
  -- the axiom A ∈ B ⇔ ∃x.(x = A ∧ x ∈ B)
  class∈class : idxCT
  -- the axiom A = B ⇔ ∀x.(x ∈ A ⇔ x ∈ B)
  class≈class : idxCT
  tmp : (C : Set) (Γ : Ctx) (x : Var Γ) (Φ : Formula C (extend Γ)) → idxCT

data two-classes : Set where
  A B : two-classes

CT : Theory
thy-idx CT = idxCT

thy-cls CT (set∈class C Γ y Φ) = C
thy-cls CT class∈class = two-classes
thy-cls CT class≈class = two-classes
thy-cls CT (tmp C Γ x Φ) = C

thy-ctx CT (set∈class C Γ y Φ) = Γ
thy-ctx CT class∈class = ⟨⟩
thy-ctx CT class≈class = ⟨⟩
thy-ctx CT (tmp C Γ x Φ) = Γ

thy-axi CT (set∈class C Γ y Φ) = svar y ∈ class Φ ⇔ Φ [ svar y ]F
thy-axi CT class∈class = cvar A ∈ cvar B ⇔ exists (svar zero ≈ cvar A ∧ svar zero ∈ cvar B)
thy-axi CT class≈class = cvar A ≈ cvar B ⇔ all (svar zero ∈ cvar A ⇔ svar zero ∈ cvar B)
thy-axi CT (tmp C Γ x Φ) = Φ [ svar x ]F ⇔ exists (svar zero ≈ svar (suc x) ∧ Φ)


-- The basic first-order set theory with Extensionality as its only axiom

data idxST : Set₁ where
  ext : (Γ : Ctx) (x : Var Γ) (y : Var Γ) → idxST
  tmp : (C : Set) (Γ : Ctx) (x : Var Γ) (Φ : Formula C (extend Γ)) → idxST

ST : Theory
thy-idx ST = idxST

thy-cls ST (ext _ _ _) = 𝟘
thy-cls ST (tmp C Γ x Φ) = C

thy-ctx ST (ext Γ _ _) = Γ
thy-ctx ST (tmp C Γ x Φ) = Γ

-- the axiom of extensionality: x = y ⇔ ∀z.(z ∈ x ⇔ z ∈ y)
thy-axi ST (ext Γ x y) = svar x ≈ svar y ⇔ all (svar zero ∈ svar (suc x) ⇔ svar zero ∈ svar (suc y))
thy-axi ST (tmp C Γ x Φ) = Φ [ svar x ]F ⇔ exists (svar zero ≈ svar (suc x) ∧ Φ)
