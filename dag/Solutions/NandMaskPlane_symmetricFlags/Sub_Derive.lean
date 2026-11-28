import Mathlib.Tactic

theorem solution (a b c d r : ℝ) (r₁ : a+b=r) (r₂ : c+d=r)
    (c₁ : a+c=r) (c₂ : b+d=r) : a=d ∧ b=c := by
  constructor <;> linarith
