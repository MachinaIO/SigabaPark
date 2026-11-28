import Mathlib

theorem solution {R : Type*} [AddCommGroup R] (v : ℕ → R) (n : ℕ) :
    (∑ i ∈ Finset.range n, (v (i+1) - v i)) = v n - v 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel
