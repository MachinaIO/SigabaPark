import Mathlib

theorem solution (x : ZMod 8) :
    (x ≠ 4 ∧ 2*x ≠ 4 ∧ x-1 ≠ 4 ∧ 2*(x-1) ≠ 4) ↔ (x = 0 ∨ x = 1) := by
  revert x
  decide
