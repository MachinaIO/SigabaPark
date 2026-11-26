import Definitions.Def_LatticeAttack_Research_Wall1_FormalLogDerivative
import Definitions.Def_LatticeAttack_Research_Wall1_LogCoefficientDerivative
import Definitions.Def_LatticeAttack_Research_Wall1_NormalizedMomentSeries

set_option autoImplicit true

/-! Formal factorial cumulants and the logarithmic canonical correction coefficients. -/
noncomputable section
namespace SigabaNeo.Wall1.FactorialMomentTransfer
open PowerSeries ExponentialCoefficientRecurrence

/-- Removing the mean exponential changes the formal logarithm only in degree one. -/
theorem log_normalizedMomentSeries (F : ℕ → ℝ) (μ : ℝ) (hF : F 0 = 1) :
    logOf (normalizedMomentSeries F) =
      mk (logarithmicCoefficient (canonicalCorrection F μ)) + C μ * X := by
  let D := correctionSeries F μ
  let E := linearExponentialSeries μ
  let L := mk (logarithmicCoefficient (canonicalCorrection F μ))
  have hc : constantCoeff (normalizedMomentSeries F) = 1 := by
    rw [constantCoeff_normalizedMomentSeries, hF]
  have hne : normalizedMomentSeries F ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    norm_num at hc
  have hd : derivative L * D = derivative D :=
    logarithmicCoefficient_derivative_mul _ (by rw [canonicalCorrection_zero, hF])
  have he : derivative E = C μ * E := derivative_linearExponentialSeries μ
  have hp : derivative (L + C μ * X) * normalizedMomentSeries F =
      derivative (normalizedMomentSeries F) := by
    rw [normalizedMomentSeries_eq_product]
    change derivative (L + C μ * X) * (D * E) = derivative (D * E)
    simp only [map_add, Derivation.leibniz, smul_eq_mul, derivative_C, derivative_X,
      mul_zero, zero_mul, mul_one, zero_add, add_zero]
    rw [he]
    calc
      _ = (derivative L * D) * E + C μ * D * E := by ring
      _ = _ := by rw [hd]; ring
  apply derivative.ext
  · apply mul_right_cancel₀ hne
    exact (derivative_logOf_mul _ hc).trans hp.symm
  · simp only [constantCoeff_logOf hc, map_add, map_mul, constantCoeff_C,
      constantCoeff_X, mul_zero, add_zero]
    exact (logarithmicCoefficient_constantCoeff _).symm

/-- Formal factorial cumulants use exponential-generating-function normalization. -/
def factorialCumulant (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * coeff n (logOf (normalizedMomentSeries F))

/-- All degrees beyond the removed linear mean retain the ordinary logarithmic coefficients. -/
theorem logarithmicCorrection_eq_cumulant (F : ℕ → ℝ) (μ : ℝ) (hF : F 0 = 1)
    {n : ℕ} (hn : 2 ≤ n) :
    logarithmicCoefficient (canonicalCorrection F μ) n =
      factorialCumulant F n / (n.factorial : ℝ) := by
  unfold factorialCumulant
  rw [log_normalizedMomentSeries F μ hF, map_add, coeff_mk, coeff_C_mul]
  have hn1 : n ≠ 1 := by omega
  simp only [coeff_X, hn1, ite_false, mul_zero, add_zero]
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

end SigabaNeo.Wall1.FactorialMomentTransfer
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.log_normalizedMomentSeries
#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.logarithmicCorrection_eq_cumulant
