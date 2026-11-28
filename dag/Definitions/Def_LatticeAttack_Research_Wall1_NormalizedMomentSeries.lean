import Definitions.Def_LatticeAttack_Research_Wall1_CanonicalNormalizedConvolution
import Mathlib.RingTheory.PowerSeries.Derivative

set_option autoImplicit true

/-! Formal generating-series product for canonical factorial corrections. -/
noncomputable section
namespace SigabaNeo.Wall1.FactorialMomentTransfer
open PowerSeries

def normalizedMomentSeries (F : ℕ → ℝ) : PowerSeries ℝ :=
  mk (fun n ↦ F n / (n.factorial : ℝ))

def correctionSeries (F : ℕ → ℝ) (μ : ℝ) : PowerSeries ℝ :=
  mk (canonicalCorrection F μ)

def linearExponentialSeries (μ : ℝ) : PowerSeries ℝ :=
  mk (fun n ↦ μ^n / (n.factorial : ℝ))

theorem normalizedMomentSeries_eq_product (F : ℕ → ℝ) (μ : ℝ) :
    normalizedMomentSeries F = correctionSeries F μ * linearExponentialSeries μ := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [normalizedMomentSeries, correctionSeries, linearExponentialSeries, coeff_mk]
    using normalized_convolution F μ n

theorem constantCoeff_normalizedMomentSeries (F : ℕ → ℝ) :
    constantCoeff (normalizedMomentSeries F) = F 0 := by
  simp [normalizedMomentSeries, ← coeff_zero_eq_constantCoeff_apply]

theorem constantCoeff_correctionSeries (F : ℕ → ℝ) (μ : ℝ) :
    constantCoeff (correctionSeries F μ) = F 0 := by
  simp [correctionSeries, ← coeff_zero_eq_constantCoeff_apply, canonicalCorrection_zero]

theorem derivative_linearExponentialSeries (μ : ℝ) :
    derivative (linearExponentialSeries μ) = C μ * linearExponentialSeries μ := by
  ext n
  simp only [linearExponentialSeries, coeff_derivative, coeff_C_mul, coeff_mk,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp

end SigabaNeo.Wall1.FactorialMomentTransfer
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.normalizedMomentSeries_eq_product
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.derivative_linearExponentialSeries
