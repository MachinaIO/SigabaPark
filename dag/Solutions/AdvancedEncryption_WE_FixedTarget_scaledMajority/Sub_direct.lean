import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution (a : ℕ → ℝ) (n : ℕ) (ha : ∀ j, 0≤a j)
    (s x : ℝ) (h0 : 0≤s) (h1 : s≤1) (x0 : 0≤x) (x1 : x≤1) :
    s*majSeries a n x ≤ majSeries a n (s*x) := by
  have hxs : s*x ≤ x := by nlinarith
  have hxs0 : 0≤s*x := mul_nonneg h0 x0
  have hx2 : 0≤1-x^2 := by nlinarith
  have hcmp : 1-x^2 ≤ 1-(s*x)^2 := by nlinarith [sq_nonneg (x-s*x),mul_nonneg (sub_nonneg.mpr hxs) (add_nonneg x0 hxs0)]
  unfold majSeries
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hxs0
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx2 hcmp j) (ha j))
