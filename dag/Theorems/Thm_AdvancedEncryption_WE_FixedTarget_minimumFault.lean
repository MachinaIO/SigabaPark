import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem AdvancedEncryption.WE.FixedTarget.minimumFault {n : ℕ} (hn : 0<n) (w : Fin n → ℝ) :
    ∃ j, n * w j ≤ ∑ i, w i := by sorry
