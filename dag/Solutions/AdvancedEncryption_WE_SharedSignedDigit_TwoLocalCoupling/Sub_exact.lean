import Mathlib

theorem solution (A B u v β : Bool) (h : (A && B) = false) :
    let u' := u ^^ !A
    let v' := v ^^ A
    ((!β ^^ u' ^^ v') = (β ^^ u ^^ v)) ∧
    ((A && u') = (A && u)) ∧ ((B && v') = (B && v)) := by
  revert A B u v β
  decide
