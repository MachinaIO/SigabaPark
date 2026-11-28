import Definitions.Def_RoleOrderLabels
import Mathlib.Tactic

theorem RoleOrderLabels.linearShift {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (b : W) :
    (∀ y, (∃ k, f k = y) ↔ (∃ k, f k + b = y)) ↔ ∃ k, f k = b := by
  sorry
