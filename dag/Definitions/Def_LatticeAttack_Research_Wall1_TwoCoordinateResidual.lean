import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit true

/-! # Convex residual for two-coordinate integer-ball counting

This scalar layer supports mean-preserving rounding in all but two coordinates.
It does not by itself prove the planar lattice count or the integrated ball bound.
-/

noncomputable section
namespace SigabaNeo.Wall1.TwoCoordinateResidual
open Real

def residual (c y : ℝ) : ℝ := (max (sqrt y - c) 0)^2

theorem residual_le_iff {c y z : ℝ} (hc : 0 ≤ c) (hz : 0 ≤ z) :
    residual c y ≤ z ↔ y ≤ (sqrt z + c)^2 := by
  unfold residual
  nth_rw 1 [← sq_sqrt hz]
  rw [sq_le_sq₀ (le_max_right _ _) (sqrt_nonneg _), max_le_iff]
  rw [and_iff_left (sqrt_nonneg z), sub_le_iff_le_add]
  exact sqrt_le_iff.trans (and_iff_right (add_nonneg (sqrt_nonneg z) hc))

theorem residual_mono (c : ℝ) : Monotone (residual c) := by
  intro x y hxy
  unfold residual
  apply pow_le_pow_left₀ (le_max_right _ _)
  exact max_le_max (sub_le_sub_right (sqrt_le_sqrt hxy) c) le_rfl

theorem residual_convex {c : ℝ} (hc : 0 ≤ c) : ConvexOn ℝ Set.univ (residual c) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  let u := max (sqrt x - c) 0
  let v := max (sqrt y - c) 0
  let z := a*u^2+b*v^2
  have hz : 0 ≤ z := add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _))
  have hx' : x ≤ (u+c)^2 := sqrt_le_iff.mp (by dsimp [u]; linarith [le_max_left (sqrt x-c) 0]) |>.2
  have hy' : y ≤ (v+c)^2 := sqrt_le_iff.mp (by dsimp [v]; linarith [le_max_left (sqrt y-c) 0]) |>.2
  have hcs : (a*u+b*v)^2 ≤ z := by
    have he : (a+b)*(a*u^2+b*v^2)-(a*u+b*v)^2 = a*b*(u-v)^2 := by ring
    rw [hab, one_mul] at he
    have hp := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u-v))
    dsimp [z]
    linarith
  have hmean : a*u+b*v ≤ sqrt z := by nlinarith [sqrt_nonneg z, sq_sqrt hz]
  change residual c (a*x+b*y) ≤ z
  apply (residual_le_iff hc hz).2
  have hw := add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
  have he : a*(u+c)^2+b*(v+c)^2 = z+2*c*(a*u+b*v)+c^2 := by
    dsimp [z]
    nlinarith [congrArg (fun t : ℝ ↦ t*c^2) hab]
  rw [he] at hw
  have hm := mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ 2*c)
  nlinarith [sq_sqrt hz]

theorem residual_lower (c y : ℝ) :
    max y 0 - 2*c*sqrt y ≤ residual c y := by
  by_cases hy : 0 ≤ y
  · rw [max_eq_left hy]
    have hs := sqrt_nonneg y
    have he := sq_sqrt hy
    by_cases h : 0 ≤ sqrt y - c
    · rw [residual, max_eq_left h]
      nlinarith [sq_nonneg c]
    · rw [residual, max_eq_right (le_of_not_ge h)]
      have hp := mul_nonneg hs (show 0 ≤ c - sqrt y by linarith)
      nlinarith
  · have hyn : y ≤ 0 := le_of_not_ge hy
    simp [residual, max_eq_right hyn, sqrt_eq_zero_of_nonpos hyn]

theorem residual_jensen {ι : Type*} (t : Finset ι) (w y : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hw : ∀ i ∈ t, 0 ≤ w i) (hws : ∑ i ∈ t, w i = 1) :
    residual c (∑ i ∈ t, w i * y i) ≤ ∑ i ∈ t, w i * residual c (y i) := by
  simpa only [smul_eq_mul] using
    (residual_convex hc).map_sum_le hw hws (fun i hi ↦ Set.mem_univ (y i))

/-- A bound on expected rounding energy suffices for the completion residual.
The energies and remaining squared radii may be negative; no clipping assumption
is needed for this scalar Jensen step. -/
theorem residual_jensen_of_energy_le {ι : Type*} (t : Finset ι)
    (w e : ι → ℝ) {c radiusSq bound : ℝ} (hc : 0 ≤ c)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hws : ∑ i ∈ t, w i = 1)
    (he : ∑ i ∈ t, w i * e i ≤ bound) :
    residual c (radiusSq - bound) ≤
      ∑ i ∈ t, w i * residual c (radiusSq - e i) := by
  have hmean : (∑ i ∈ t, w i * (radiusSq - e i)) =
      radiusSq - ∑ i ∈ t, w i * e i := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hws, one_mul]
  apply le_trans ?_ (residual_jensen t w (fun i ↦ radiusSq - e i) hc hw hws)
  rw [hmean]
  exact residual_mono c (sub_le_sub_left he radiusSq)

end SigabaNeo.Wall1.TwoCoordinateResidual
#print axioms SigabaNeo.Wall1.TwoCoordinateResidual.residual_convex

#print axioms SigabaNeo.Wall1.TwoCoordinateResidual.residual_lower
#print axioms SigabaNeo.Wall1.TwoCoordinateResidual.residual_jensen

#print axioms SigabaNeo.Wall1.TwoCoordinateResidual.residual_jensen_of_energy_le
