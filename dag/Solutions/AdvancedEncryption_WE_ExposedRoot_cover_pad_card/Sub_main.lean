import Mathlib.Data.Matrix.Mul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Common

theorem solution {R : Type*} [Ring R] [Fintype R] {n k : Type*}
    [Fintype n] [DecidableEq n] [Fintype k]
    (M Minv : Matrix n n R) (h1 : M * Minv = 1) (h2 : Minv * M = 1)
    (x t : Matrix n k R) :
    Nat.card {u : Matrix n k R // x + M * u = t} = 1 := by
  have key : ∀ u : Matrix n k R, x + M * u = t → u = Minv * (t - x) := by
    intro u hu
    rw [← hu, add_sub_cancel_left, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ((key _ a.2).trans (key _ b.2).symm)⟩, ⟨⟨Minv * (t - x), ?_⟩⟩⟩
  rw [← Matrix.mul_assoc, h1, Matrix.one_mul, add_sub_cancel]
