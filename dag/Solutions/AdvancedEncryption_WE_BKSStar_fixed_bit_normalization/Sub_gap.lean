import Mathlib

theorem solution (u v common : ℝ) :
    |(1 - u + common) / 2 - (1 - v + common) / 2| =
      |(1 - u + v) / 2 - 1 / 2| ∧
    |(1 - u + v) / 2 - 1 / 2| = |v - u| / 2 := by
  have h1 : (1 - u + common) / 2 - (1 - v + common) / 2 = (v - u) / 2 := by ring
  have h2 : (1 - u + v) / 2 - 1 / 2 = (v - u) / 2 := by ring
  rw [h1, h2, abs_div]
  norm_num
