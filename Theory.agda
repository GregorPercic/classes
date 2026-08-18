open import Syntax
open import Substitutions


record theory : Set₁ where
  field
    thy-idx : Set -- axiom names
    thy-ctx : thy-idx → Ctx -- set variables appearing in the axiom
    thy-axi : ∀ (i : thy-idx) → formula (thy-ctx i)

open theory public


-- The basic first-order set theory with Extensionality as its only axiom

data idxST : Set where
  ext : idxST

ST : theory
thy-idx ST = idxST

thy-ctx ST ext = ⟨⟩

-- the axiom of extensionality: ∀x∀y.(x = y ⇔ ∀z.(z ∈ x ⇔ z ∈ y))
thy-axi ST ext = all (all (svar (suc zero) ≈ svar zero ⇔ all (svar zero ∈ svar (suc (suc zero)) ⇔ svar zero ∈ svar (suc zero))))