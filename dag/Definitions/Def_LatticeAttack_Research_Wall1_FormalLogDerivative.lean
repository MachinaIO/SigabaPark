import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit true

/-! Formal logarithmic differentiation at constant term one. No analytic or probabilistic
hypotheses are needed. -/
noncomputable section
namespace SigabaNeo.Wall1.ExponentialCoefficientRecurrence
open PowerSeries

/-- The formal logarithm satisfies its derivative product identity for a normalized series. -/
theorem derivative_logOf_mul (f : PowerSeries ℝ) (hf : constantCoeff f = 1) :
    derivative (logOf f) * f = derivative f := by
  have hs : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hi : (derivative (PowerSeries.log ℝ)).subst (f - 1) * f = 1 := by
    have h := congrArg (fun g : PowerSeries ℝ ↦ g.subst (f - 1))
      (derivative_log_mul_one_add_X (A := ℝ))
    rw [subst_mul hs, subst_add hs, subst_X hs] at h
    have h1 : (1 : PowerSeries ℝ).subst (f - 1) = 1 := by
      rw [← coe_substAlgHom hs, map_one]
    rw [h1] at h
    convert h using 1; ring
  rw [logOf_eq, derivative_subst hs, map_sub, derivative_one, sub_zero]
  calc
    (derivative (PowerSeries.log ℝ)).subst (f - 1) * derivative f * f =
        ((derivative (PowerSeries.log ℝ)).subst (f - 1) * f) * derivative f := by ring
    _ = derivative f := by rw [hi, one_mul]

end SigabaNeo.Wall1.ExponentialCoefficientRecurrence
