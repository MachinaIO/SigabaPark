import Mathlib

theorem solution (a : ℤ) :
    (1+a+a^2+a^3)*(a-1) = (a^4+1)-2 := by
  ring
