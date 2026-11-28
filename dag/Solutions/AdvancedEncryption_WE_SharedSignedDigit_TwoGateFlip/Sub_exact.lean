import Mathlib

theorem solution (x y z : Bool) (hz : z = true ∧ (x = false ∨ y = false)) :
    (let d : ZMod 16 := 4 * (if x then 0 else 1) + (if z then 0 else 1)
     let e : ZMod 16 := 4 * (if y then 0 else 1) + 2 * (if z then 0 else 1)
     ∃ p r : Bool, ∀ a b : Bool,
       (if a ^^ p then d else -d) + (if b ^^ r then e else -e) =
       8 + (if a then d else -d) + (if b then e else -e)) := by
  revert x y z
  decide
