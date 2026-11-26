import Definitions.Def_LatticeAttack_Research_Wall1_NormalizedMomentSeries

set_option autoImplicit true

/-! The factorial-moment series of a finite uniform law is its shifted generating
function. Empty sample types are allowed: both sides then vanish. -/
noncomputable section
namespace SigabaNeo.Wall1.FactorialMomentTransfer
open Finset PowerSeries

theorem coeff_one_add_X_pow_real (m j : ℕ) :
    coeff j ((1 + X : PowerSeries ℝ)^m) = (m.choose j : ℝ) := by
  have h := Polynomial.coeff_one_add_X_pow ℝ m j
  simpa only [← Polynomial.coeff_coe, Polynomial.coe_pow, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_X] using h

/-- No independence assumption is needed: this is the generating function of
the given joint finite law itself. -/
theorem normalizedMomentSeries_factorialAverage {Ω α : Type*}
    [Fintype Ω] [Fintype α] (n : Ω → α → ℕ) :
    normalizedMomentSeries (factorialAverage n) =
      (((Fintype.card Ω : ℝ) * Fintype.card α)⁻¹) •
        (∑ ω, ∑ c, (1 + X : PowerSeries ℝ)^(n ω c)) := by
  ext j
  simp only [normalizedMomentSeries, coeff_mk, factorialAverage, map_smul,
    map_sum, smul_eq_mul, coeff_one_add_X_pow_real]
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  simp_rw [← mul_sum]
  have hj : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  rw [div_right_comm, mul_div_cancel_left₀ _ hj, div_eq_mul_inv, mul_comm]

end SigabaNeo.Wall1.FactorialMomentTransfer

#print axioms SigabaNeo.Wall1.FactorialMomentTransfer.normalizedMomentSeries_factorialAverage
