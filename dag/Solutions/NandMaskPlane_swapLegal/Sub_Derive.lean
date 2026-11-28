import Mathlib.Tactic

theorem solution : ∀ a x y z : Bool,
    ((x && y) = (a && (xor a z))) ↔
    ((xor x a && xor y a) = (a && xor a (xor (xor (xor z x) y) a))) := by
  decide
