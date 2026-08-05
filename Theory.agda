open import Syntax
open import Substitutions


record theory : Set₂ where
  field
    thy-idx : Set₁ -- axiom names
    thy-ctx : thy-idx → Ctx -- set variables appearing in the axiom
    thy-axi : ∀ (i : thy-idx) → formula (thy-ctx i)

open theory public


-- The basic first-order set theory with Extensionality as its only axiom

data idxST : Set₁ where
  ext : (Γ : Ctx) (x : Var Γ) (y : Var Γ) → idxST

ST : theory
thy-idx ST = idxST

thy-ctx ST (ext Γ _ _) = Γ

-- the axiom of extensionality: x = y ⇔ ∀z.(z ∈ x ⇔ z ∈ y)
thy-axi ST (ext Γ x y) = svar x ≈ svar y ⇔ all (svar zero ∈ svar (suc x) ⇔ svar zero ∈ svar (suc y))