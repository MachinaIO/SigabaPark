import Definitions.Def_LatticeAttack_Research_Wall1_CanonicalFactorialCorrection

set_option autoImplicit true

/-! # The second canonical factorial correction

These identities expose the exact second-order discrepancy. They do not bound
that discrepancy for any particular count distribution.
-/

noncomputable section
namespace SigabaNeo.Wall1.FactorialMomentTransfer
open Finset

/-- The second coefficient of the canonical triangular inversion. -/
theorem canonicalCorrection_two (F : ℕ → ℝ) (μ : ℝ) :
    canonicalCorrection F μ 2 = (F 2 - 2 * μ * F 1 + μ^2 * F 0) / 2 := by
  rw [canonicalCorrection_eq]
  norm_num [sum_range_succ, canonicalCorrection_zero, canonicalCorrection_one,
    transferCoefficient, Nat.factorial]
  ring

/-- For normalized constant and first moments, only the second factorial discrepancy remains. -/
theorem canonicalCorrection_two_normalized (F : ℕ → ℝ) (μ : ℝ)
    (hzero : F 0 = 1) (hone : F 1 = μ) :
    canonicalCorrection F μ 2 = (F 2 - μ^2) / 2 := by
  rw [canonicalCorrection_two, hzero, hone]
  ring

end SigabaNeo.Wall1.FactorialMomentTransfer

#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.canonicalCorrection_two
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.canonicalCorrection_two_normalized
