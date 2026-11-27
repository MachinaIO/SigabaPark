import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

theorem solution
    {V G : Type*} [SeminormedAddCommGroup V] [AddCommGroup G]
    (A : V →+ G) (s u v : G) (x y z : V) (B : ℝ)
    (hx : A x = s) (hy : A y = s + u + v) (hz : A z = s + 3 • u + 9 • v)
    (bx : ‖x‖ ≤ B) (by' : ‖y‖ ≤ B) (bz : ‖z‖ ≤ B) :
    A (x + z + z - y - y) = s + 4 • u + 16 • v ∧ ‖x + z + z - y - y‖ ≤ 5 * B := by
  constructor
  · simp only [map_sub, map_add, hx, hy, hz]
    abel
  · linarith [norm_add_le x z, norm_add_le (x + z) z,
      norm_sub_le (x + z + z) y, norm_sub_le (x + z + z - y) y]
