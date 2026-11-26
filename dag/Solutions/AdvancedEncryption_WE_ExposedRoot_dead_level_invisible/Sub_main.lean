import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] {a n : Type*} [Fintype n]
    (P : ℕ → Set (Matrix a n R)) (N0 N1 : ℕ → Matrix n n R)
    (hstep : ∀ i v, v ∈ P (i + 1) → ∃ u0 ∈ P i, ∃ u1 ∈ P i, v = u0 * N0 i + u1 * N1 i)
    (j : ℕ) (hdead0 : N0 j = 0) (hdead1 : N1 j = 0) :
    ∀ i, j < i → ∀ v ∈ P i, v = 0 := by
  intro i hi
  induction i with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ i ih =>
    intro v hv
    obtain ⟨u0, hu0, u1, hu1, rfl⟩ := hstep i v hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [ih h u0 hu0, ih h u1 hu1, Matrix.zero_mul, Matrix.zero_mul, add_zero]
    · subst h
      rw [hdead0, hdead1, Matrix.mul_zero, Matrix.mul_zero, add_zero]
