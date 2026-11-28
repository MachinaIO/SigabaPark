import Mathlib

theorem solution (a b : ℚ) :
    let step : ℚ × ℚ → ℚ × ℚ := fun v ↦ ((v.1-v.2)/2,(v.1+v.2)/2)
    let q := step (step (a,b))
    |q.1| + |q.2| = (|a|+|b|)/2 := by
  change |((a-b)/2-(a+b)/2)/2| + |((a-b)/2+(a+b)/2)/2| = _
  have h1 : ((a-b)/2-(a+b)/2)/2 = -b/2 := by ring
  have h2 : ((a-b)/2+(a+b)/2)/2 = a/2 := by ring
  rw [h1,h2,abs_div,abs_div,abs_neg]
  norm_num
  ring
