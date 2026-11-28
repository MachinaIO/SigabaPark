import Definitions.Def_LatticeAttack_Research_Wall1_BallSliceIntegrals
import Definitions.Def_LatticeAttack_Research_Wall1_TwoCoordinateEmbedding

set_option autoImplicit true

/-! The explicit two-coordinate volume lower bound for the full integer ball. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open Finset MeasureTheory TwoCoordinateResidual

/-- The sharp lower count before centered-coordinate exclusions. -/
theorem closedLifts_two_coordinate_lower {n : ℕ} {R a : ℝ}
    (hR : 0 ≤ R) (ha : 0 ≤ a) (ha2 : a^2 = R^2 - (n : ℝ)/4) :
    unitVolume (n+2) * a^(n+2) -
      (Real.pi / Real.sqrt 2) * (unitVolume (n+1) * a^(n+1)) ≤
      ((closedLifts (n+2) R).card : ℝ) := by
  let f (x : Fin n → ℝ) := Real.pi * max (a^2 - ∑ i, (x i)^2) 0
  let g (x : Fin n → ℝ) :=
    (Real.pi / Real.sqrt 2) * (2 * Real.sqrt (max (a^2 - ∑ i, (x i)^2) 0))
  let h (x : Fin n → ℝ) := Real.pi * residual (1 / Real.sqrt 2)
    (R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4))
  have hf : Integrable f := quadratic_slice_integrable n ha
  have hg : Integrable g := (sqrt_slice_integrable n ha).const_mul _
  have hh : Integrable h :=
    (radial_residual_integrable R (1 / Real.sqrt 2) hR (by positivity)).const_mul _
  have hpt (x : Fin n → ℝ) : f x - g x ≤ h x := by
    have hs (y : ℝ) : Real.sqrt (max y 0) = Real.sqrt y := by
      rw [← Real.sq_sqrt', Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have he : R^2 - ((∑ i, (x i)^2) + (n : ℝ)/4) = a^2 - ∑ i, (x i)^2 := by
      rw [ha2]
      ring
    have hb := mul_le_mul_of_nonneg_left
      (residual_lower (1 / Real.sqrt 2) (a^2 - ∑ i, (x i)^2)) Real.pi_nonneg
    dsimp [f, g, h]
    rw [he, hs]
    convert hb using 1 <;> ring
  have hi := integral_mono (hf.sub hg) hh hpt
  have hfval : (∫ x, f x) = unitVolume (n+2) * a^(n+2) := quadratic_slice_integral n ha
  have hgval : (∫ x, g x) =
      (Real.pi / Real.sqrt 2) * (unitVolume (n+1) * a^(n+1)) := by
    dsimp [g]
    rw [integral_const_mul, sqrt_slice_integral n ha]
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hf hg, hfval, hgval] at hi
  exact hi.trans (two_coordinate_integral_lower hR)

end SigabaNeo.Wall1.RawBallRounding
#print axioms SigabaNeo.Wall1.RawBallRounding.closedLifts_two_coordinate_lower
