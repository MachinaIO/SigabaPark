import Mathlib

theorem solution (u v : ℤ) (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1) :
    ((1-u*v) + (1-(1-u)*(1-v)) - (1-(1-u)*v) - (1-u*(1-v)))^2 = 1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> norm_num
