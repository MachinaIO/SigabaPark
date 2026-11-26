module

public import CslibFrontier.Foundations.Probability.Gaussian.Poisson
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic

set_option autoImplicit true

/-! # Absolute Poisson estimate for complex radial Gaussians on a Euclidean lattice -/

public section
noncomputable section
namespace SigabaNeo.Wall1

open MeasureTheory ProbabilityTheory Module Filter Asymptotics ZLattice
open scoped FourierTransform Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem summable_radial_gaussian (D : Submodule ℤ E) [DiscreteTopology D]
    {a : ℝ} (ha : 0 < a) : Summable (fun x : D ↦ Real.exp (-a*‖x.val‖^2)) := by
  let s := Real.sqrt (Real.pi/a)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos Real.pi_pos ha)
  refine (summable_gaussianWeight D s hs 0).congr fun x ↦ ?_
  simp only [gaussianWeight, sub_zero, s, Real.sq_sqrt (by positivity : 0 ≤ Real.pi/a)]
  congr 1
  field_simp

/-- The Gaussian parameter can be any complex number in the open right half-plane.
The dual exponent is the real part of π²/b. -/
theorem complex_gaussian_poisson_bound (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {b : ℂ} (hb : 0 < b.re) :
    ‖∑' x : L, Complex.exp (-b * ‖x.val‖^2)‖ ≤
      ((Real.pi / ‖b‖) ^ ((finrank ℝ E : ℝ)/2)) / covolume L *
        ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          Real.exp (-(Real.pi^2 / b).re * ‖w.val‖^2) := by
  let D := LinearMap.BilinForm.dualSubmodule (innerₗ E) L
  let := discreteTopology_dualSubmodule L
  let a : ℝ := ((Real.pi : ℂ)^2 / b).re
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have ha : 0 < a := by
    dsimp [a]
    rw [Complex.div_re]
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      zero_div, add_zero]
    positivity [Complex.normSq_pos.mpr hb0]
  let f : C(E, ℂ) := ⟨fun x ↦ Complex.exp (-b * ‖x‖^2), by fun_prop⟩
  have hn (x : E) : ‖f x‖ = Real.exp (-b.re * ‖x‖^2) := by
    simp [f, Complex.norm_exp, ← Complex.ofReal_pow, Complex.mul_re]
  have hd : f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-((finrank ℤ L : ℝ) + 1))) := by
    apply isBigO_norm_left.mp
    simp only [hn]
    have h := (rexp_neg_quadratic_isLittleO_rpow_atTop (neg_lt_zero.mpr hb) 0
      (-((finrank ℤ L : ℝ)+1))).comp_tendsto (tendsto_norm_cocompact_atTop (E := E))
    simpa only [Function.comp_def, zero_mul, add_zero] using h.isBigO
  have hi : Integrable (f : E → ℂ) := by
    simpa [f] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0:E)
  let c := (Real.pi / ‖b‖) ^ ((finrank ℝ E : ℝ)/2)
  have hfourier (w : E) : ‖𝓕 (f : E → ℂ) w‖ = c * Real.exp (-a * ‖w‖^2) := by
    change ‖𝓕 (fun x : E ↦ Complex.exp (-b * ‖x‖^2)) w‖ = _
    rw [fourier_gaussian_innerProductSpace hb, norm_mul, Complex.norm_exp]
    have he : -(Real.pi : ℂ)^2 * (‖w‖ : ℂ)^2 / b =
        -((Real.pi : ℂ)^2 / b) * ((‖w‖^2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re]
    congr 1
    rw [show (finrank ℝ E : ℂ)/2 = (((finrank ℝ E : ℝ)/2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_real, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hsum : Summable fun w : D ↦ ‖𝓕 (f : E → ℂ) w.val‖ := by
    simp only [hfourier]
    exact (summable_radial_gaussian D ha).mul_left c
  have hp := tsum_eq_tsum_fourier_of_rpow_decay L f (by linarith : (finrank ℤ L : ℝ) <
    finrank ℤ L + 1) hd hi hsum.of_norm (0:E)
  simp at hp
  change ‖∑' x : L, f x.val‖ ≤ _
  rw [hp, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (covolume_pos L volume)]
  calc
    _ ≤ (covolume L)⁻¹ * ∑' w : D, ‖𝓕 (f : E → ℂ) w.val‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum) (by positivity [covolume_pos L volume])
    _ = c / covolume L * ∑' w : D, Real.exp (-a * ‖w.val‖^2) := by
      simp only [hfourier, tsum_mul_left, div_eq_mul_inv]
      ring

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.complex_gaussian_poisson_bound
