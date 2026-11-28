import Definitions.Def_LatticeAttack_Research_Wall1_TwoCoordinateResidual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit true

/-! Integrability of the residual used in two-coordinate ball counting. -/
noncomputable section
namespace SigabaNeo.Wall1.TwoCoordinateResidual
open MeasureTheory Finset

/-- The residual is continuous even when the available squared radius is negative. -/
theorem residual_continuous (c : ℝ) : Continuous (residual c) := by
  unfold residual
  fun_prop

/-- The rounding correction leaves a compactly supported radial function. -/
theorem radial_residual_integrable {n : ℕ} (R c : ℝ) (hR : 0 ≤ R) (hc : 0 ≤ c) :
    Integrable (fun x : Fin n → ℝ ↦
      residual c (R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4))) := by
  have hcont : Continuous (fun x : Fin n → ℝ ↦
      residual c (R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4))) := by
    apply (residual_continuous c).comp
    fun_prop
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro
    (isCompact_univ_pi (fun _ : Fin n ↦ isCompact_Icc (a := -R) (b := R)))
  intro x hx
  have hout : ∃ i, x i < -R ∨ R < x i := by
    simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc,
      not_forall, not_and_or, not_le] using hx
  obtain ⟨i, hi⟩ := hout
  have hs : (x i)^2 ≤ ∑ j, (x j)^2 :=
    single_le_sum (fun j _ ↦ sq_nonneg (x j)) (mem_univ i)
  have hn : (0 : ℝ) ≤ (n : ℝ)/4 := by positivity
  have hneg : R^2 - ((∑ j, (x j)^2) + (n : ℝ)/4) ≤ 0 := by
    rcases hi with hi | hi <;> nlinarith
  simp [residual, Real.sqrt_eq_zero_of_nonpos hneg, max_eq_right (neg_nonpos.mpr hc)]

#print axioms radial_residual_integrable
end SigabaNeo.Wall1.TwoCoordinateResidual
