import Mathlib.Data.Bool.Basic

theorem solution (normal y v k0 k1 p : Bool) :
    let t0 := fun b => (if normal then v else b) ^^ k0
    let t1 := fun b => (if normal then b else v) ^^ k1
    let point := fun b => t0 b ^^ t1 b
    (t0 y ^^ (p && point y) ^^ (if p then k1 else k0) =
      if p == normal then y else v) ∧ point (!y) = !(point y) := by
  cases normal <;> cases y <;> cases v <;> cases k0 <;> cases k1 <;> cases p <;> decide
