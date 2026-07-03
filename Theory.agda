open import Syntax

record Theory : Set₁ where
  field
    thy-idx : Set -- axiom names
    thy-cls : thy-idx → Set -- class variables appearing in the axiom
    thy-ctx : thy-idx → Ctx -- set variables appearing in the axiom
    thy-axi : ∀ (i : thy-idx) → Formula (thy-cls i) (thy-ctx i)

open Theory public