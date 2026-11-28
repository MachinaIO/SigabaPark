import Mathlib

theorem solution {R : Type*} [AddCommGroup R] (old change tag0 tag1 : R) (bit : Bool) :
    (if bit then -(old+change)+(tag1+change) else old+change+(tag0-change)) =
    (if bit then -old+tag1 else old+tag0) := by
  cases bit <;> simp <;> abel
