import Mathlib

theorem solution (p₀ p₁ outside : ℚ) :
    (p₀+outside)/2 - (p₁+outside)/2 = (p₀-p₁)/2 := by
  ring
