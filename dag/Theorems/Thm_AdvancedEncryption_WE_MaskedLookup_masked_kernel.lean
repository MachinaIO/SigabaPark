import Mathlib
open scoped BigOperators

theorem AdvancedEncryption.WE.MaskedLookup.masked_kernel {I : Type} [Fintype I] [DecidableEq I] (theta : I → Bool) (kernel : (I → Bool) → ℝ) :
    (∑ pi : I → Bool, kernel (fun i ↦ theta i ^^ pi i)) = ∑ alpha : I → Bool, kernel alpha := by sorry
