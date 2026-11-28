import Mathlib

theorem solution (a b t : Bool) :
    (a ^^ (t && (a ^^ b))) = (if t then b else a) := by
  revert a b t
  decide
