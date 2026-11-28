import Mathlib

theorem solution (u v : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u + v/2 ≤ u+v ∧ u+v ≤ 2*(u+v/2) := by
  constructor <;> linarith
