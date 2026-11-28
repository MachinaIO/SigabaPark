import Mathlib

theorem solution (a b l r : ℚ) :
    ((a+b)/2)*l + ((a-b)/2)*r =
    a*((l+r)/2) + b*((l-r)/2) := by
  ring
