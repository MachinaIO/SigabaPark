import Mathlib

theorem solution (honest0 honest1 sim0 sim1 err tv0 tv1 hit : ℝ)
    (correct0 : honest0 ≤ err) (correct1 : 1 - err ≤ honest1)
    (left : |sim0 - honest0| ≤ tv0) (right : |sim1 - honest1| ≤ tv1 + hit) :
    1 - 2*err - tv0 - tv1 - hit ≤ sim1 - sim0 := by
  obtain ⟨_, h0⟩ := abs_le.mp left
  obtain ⟨h1, _⟩ := abs_le.mp right
  linarith
