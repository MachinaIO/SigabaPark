import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] [Fintype R] [DecidableEq R] {n k : Type*}
    [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (M Minv : Matrix n n R) (h1 : M * Minv = 1) (h2 : Minv * M = 1)
    (x t : Matrix n k R) :
    (Finset.univ.filter (fun u : Matrix n k R => x + M * u = t)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨Minv * (t - x), ?_⟩
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    rw [← h, add_sub_cancel_left, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  · intro h
    rw [h, ← Matrix.mul_assoc, h1, Matrix.one_mul, add_sub_cancel]
