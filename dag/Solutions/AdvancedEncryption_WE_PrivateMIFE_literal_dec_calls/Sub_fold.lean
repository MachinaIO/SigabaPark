import Mathlib

theorem solution (D : ℕ → ℕ) (hbase : D 0 = 1)
    (hstep : ∀ j, D (j + 1) = 2 * D j + 1) (j : ℕ) :
    D j + 1 = 2 ^ (j + 1) := by
  induction j with
  | zero => simp [hbase]
  | succ j ih =>
    rw [hstep, pow_succ _ (j + 1)]
    omega
