import Mathlib

theorem solution (x y z : Bool) :
    (let d : ZMod 16 := 4 * (if x then 0 else 1) + (if z then 0 else 1)
     let e : ZMod 16 := 4 * (if y then 0 else 1) + 2 * (if z then 0 else 1)
     ∃ a b c f : Bool,
       (if a then d else -d) + (if b then e else -e) =
       8 + (if c then d else -d) + (if f then e else -e)) ↔
      (z = true ∧ (x = false ∨ y = false)) := by
  revert x y z
  decide
