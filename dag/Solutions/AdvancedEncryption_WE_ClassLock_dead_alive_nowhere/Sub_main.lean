import Mathlib.Tactic.Common

theorem solution (m : ℕ → Bool → Bool) (j : ℕ) (hdead : ∀ β, m j β = false)
    (x : ℕ → Bool) : ¬ ∀ i, m i (x i) = true := by
  intro h
  have := h j
  rw [hdead] at this
  exact Bool.false_ne_true this
