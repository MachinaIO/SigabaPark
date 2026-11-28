import Definitions.Def_LatticeAttack_Research_Wall1_FormalCumulantBridge

set_option autoImplicit true

/-! The exact third factorial cumulant of a normalized moment sequence.
This identity does not assume bounds on any raw or connected incidence moment. -/
noncomputable section
namespace SigabaNeo.Wall1.ExponentialCoefficientRecurrence
open Finset

/-- The third ordinary coefficient of the formal logarithm. -/
theorem logarithmicCoefficient_three (d : ℕ → ℝ) :
    logarithmicCoefficient d 3 = d 3 - d 1 * d 2 + d 1 ^ 3 / 3 := by
  rw [show 3 = 2+1 from rfl, logarithmicCoefficient_succ]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num only at *
  rw [logarithmicCoefficient_one, logarithmicCoefficient_two]
  ring

end SigabaNeo.Wall1.ExponentialCoefficientRecurrence

namespace SigabaNeo.Wall1.FactorialMomentTransfer
open Finset ExponentialCoefficientRecurrence

private theorem canonicalCorrection_two_at_zero (F : ℕ → ℝ) :
    canonicalCorrection F 0 2 = F 2 / 2 := by
  rw [canonicalCorrection_eq]
  norm_num [sum_range_succ, transferCoefficient]

private theorem canonicalCorrection_three_at_zero (F : ℕ → ℝ) :
    canonicalCorrection F 0 3 = F 3 / 6 := by
  rw [canonicalCorrection_eq]
  norm_num [sum_range_succ, transferCoefficient]

/-- The third factorial cumulant in raw factorial-moment normalization. -/
theorem factorialCumulant_three (F : ℕ → ℝ) (hF : F 0 = 1) :
    factorialCumulant F 3 = F 3 - 3 * F 1 * F 2 + 2 * (F 1)^3 := by
  have h := logarithmicCorrection_eq_cumulant F 0 hF (n := 3) (by norm_num)
  rw [logarithmicCoefficient_three, canonicalCorrection_three_at_zero,
    canonicalCorrection_two_at_zero, canonicalCorrection_one] at h
  norm_num at h
  linarith

end SigabaNeo.Wall1.FactorialMomentTransfer
