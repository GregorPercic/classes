open import Syntax
open import Substitutions


record theory : Set₁ where
  field
    -- axiom names
    thy-idx : Set
    -- set variables appearing in the axiom
    thy-ctx : thy-idx → Ctx
    -- axiom formula
    thy-axi : (i : thy-idx) → formula (thy-ctx i)

open theory public


-- The basic first-order set theory with Extensionality as its only axiom

ST : theory

data idxST : Set where
  -- the axiom of extensionality:
  -- ∀x∀y.(x = y ⇔ ∀z.(z ∈ x ⇔ z ∈ y))
  ext : idxST

thy-idx ST = idxST
thy-ctx ST ext = ⟨⟩
thy-axi ST ext =
  all (all
    (svar (suc zero) ≈ svar zero
      ⇔
    all
      (svar zero ∈ svar (suc (suc zero))
        ⇔
      svar zero ∈ svar (suc zero))))