import Definitions.Def_LatticeAttack_Research_Wall1_CanonicalLogCoefficients
import Mathlib.RingTheory.PowerSeries.Derivative

set_option autoImplicit true

/-! Formal derivative characterization of the canonical logarithmic coefficients. -/
noncomputable section
namespace SigabaNeo.Wall1.ExponentialCoefficientRecurrence
open Finset

/-- The canonical logarithmic series has zero constant coefficient. -/
theorem logarithmicCoefficient_constantCoeff (d : ℕ → ℝ) :
    PowerSeries.constantCoeff (PowerSeries.mk (logarithmicCoefficient d)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
    logarithmicCoefficient_zero]

/-- The triangular logarithmic recurrence is exactly the formal logarithmic derivative. -/
theorem logarithmicCoefficient_derivative_mul (d : ℕ → ℝ) (hd : d 0 = 1) :
    PowerSeries.derivative (PowerSeries.mk (logarithmicCoefficient d)) * PowerSeries.mk d =
      PowerSeries.derivative (PowerSeries.mk d) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  have h := logarithmicCoefficient_recurrence d hd (n+1) (by omega)
  rw [Nat.add_sub_cancel] at h
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
    ((i+1 : ℕ) : ℝ) * logarithmicCoefficient d (i+1) * d (n-i)) (n+1)] at h
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hh := (eq_div_iff hn).mp h
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using hh.symm

end SigabaNeo.Wall1.ExponentialCoefficientRecurrence
#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.logarithmicCoefficient_constantCoeff
#print axioms SigabaNeo.Wall1.ExponentialCoefficientRecurrence.logarithmicCoefficient_derivative_mul
