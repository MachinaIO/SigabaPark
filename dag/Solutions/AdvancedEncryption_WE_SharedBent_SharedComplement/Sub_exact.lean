import Mathlib

theorem solution (a b c : ZMod 2) :
    let q : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 := fun x y z ↦ x*y+y*z+z*x
    q (a+1) (b+1) (c+1) = q a b c + 1 ∧
    q (a+1) (b+1) c + q (a+1) b c + q a (b+1) c + q a b c = 1 := by
  revert a b c
  decide
