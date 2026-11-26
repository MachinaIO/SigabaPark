import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **The targets of the BASIS_struct hints have no zero row.** In the equivalent form of the
BASIS_struct assumption (Wee–Wu, ePrint 2022/1515, §6.1) the hints are preimages
`A^{-1}(W_i^{-1} R)` with `W_i` invertible and `R` uniform (of full row rank). A row combination
`c` that vanishes on one target `W_i^{-1} R` is zero. So a single BASIS_struct hint is never a
preimage of a target with a zero (or exactly vanishing) row, which is what the children of the
hidden row of `ML_i` need (note `pq-we-hinted-lattice-assumptions`, §3). -/
theorem AdvancedEncryption.WE.Hints.basis_struct_no_zero_row {K ι μ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype μ] (W : Matrix ι ι K) (hW : IsUnit W.det)
    (Rm : Matrix ι μ K) (Rr : Matrix μ ι K) (hR : Rm * Rr = 1) (c : ι → K)
    (hc : c ᵥ* (W⁻¹ * Rm) = 0) : c = 0 := by sorry
