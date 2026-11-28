import Mathlib

theorem solution (x y : ZMod 2) : x*y = (1 + (x+y))*x := by
  have hx : x*x=x := by exact (by decide : ∀ a : ZMod 2, a*a=a) x
  have two : (2:ZMod 2)=0 := by decide
  calc
    x*y = 2*x + x*y := by rw [two]; ring
    _ = (1 + (x+y))*x := by linear_combination -hx
