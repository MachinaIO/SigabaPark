import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    |(a+b)/2| + |(a-b)/2| = max a b := by
  have hp : 0≤(a+b)/2 := by positivity
  rw [abs_of_nonneg hp]
  rcases le_total a b with h|h
  · rw [max_eq_right h, abs_of_nonpos (by linarith : (a-b)/2≤0)]
    ring
  · rw [max_eq_left h,abs_of_nonneg (by linarith : 0≤(a-b)/2)]
    ring
