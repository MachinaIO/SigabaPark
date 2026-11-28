import Mathlib
/-- The missing degree detects precisely opposite tags of a single variable. -/
theorem solution (N i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ N) (hj : 1 ≤ j) (hj' : j ≤ N) :
    (i + (3*N-j) = 3*N ↔ i = j) ∧ i+j < 3*N ∧ 3*N < (3*N-i)+(3*N-j) := by
  omega
