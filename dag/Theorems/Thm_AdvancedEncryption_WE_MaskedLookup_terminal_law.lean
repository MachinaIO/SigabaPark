import Mathlib
open scoped BigOperators

theorem AdvancedEncryption.WE.MaskedLookup.terminal_law {I : Type} [Fintype I] [DecidableEq I] (active truth cell : I → Bool)
    (test : (I → Bool) → ℝ) :
    (∑ v : I → Bool, test (fun i ↦ if active i then cell i else truth i ^^ v i)) =
      ∑ v : I → Bool, test (fun i ↦ if active i then cell i else v i) := by sorry
