import Mathlib

theorem solution (a b c x y z : Bool) :
    (((a && x) ^^ (b && y)) ^^ (c && z)) ^^ (((a ^^ b) ^^ c) && ((x ^^ y) ^^ z)) =
      ((a ^^ b) && (x ^^ z)) ^^ ((a ^^ c) && (x ^^ y)) := by
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;> decide
