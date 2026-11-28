import Mathlib.Tactic

theorem solution (pp pn np nn : ℝ) (hn : 0 ≤ nn)
    (total : pp + pn + np + nn = 1) (zero : pp - pn - np + nn = 0) :
    (pp + pn - np - nn) + (pp - pn + np - nn) ≤ 1 ∧
    ((pp + pn - np - nn) + (pp - pn + np - nn) = 1 ↔ nn = 0) := by
  constructor
  · linarith
  · constructor <;> intro h <;> linarith
