import Mathlib

theorem solution (pad edge message : Bool) :
    Bool.xor (Bool.xor pad message) edge = Bool.xor (Bool.xor pad edge) message := by
  cases pad <;> cases edge <;> cases message <;> decide
