import Mathlib

theorem solution (a b z : Bool) :
    let u : Bool → ℤ := fun x => if x then 1 else 0
    let r := u z + u a * u b - 1
    (r % 2 != 0) = (z ^^ !(a && b)) := by
  cases a <;> cases b <;> cases z <;> decide
