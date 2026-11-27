import Mathlib

theorem solution (key pad other msg : Bool) :
    xor (xor (!key) (!pad)) other = xor (xor key pad) other ∧ xor (!msg) (!key) = xor msg key := by
  cases key <;> cases pad <;> cases other <;> cases msg <;> decide
