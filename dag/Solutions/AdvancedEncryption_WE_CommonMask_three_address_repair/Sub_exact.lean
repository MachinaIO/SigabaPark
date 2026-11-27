import Mathlib

theorem solution (x y : Bool) :
    let u := x
    let v := (!x) && y
    let t := !(x || y)
    (u ^^ v ^^ t = true) ∧ (x = false → u = false) ∧
      (y = false → v = false) ∧ ((x || y) = true → t = false) := by
  cases x <;> cases y <;> decide
