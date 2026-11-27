import Mathlib

theorem solution {X : Type} [Fintype X] (u v w : X → Bool) :
    (∑ z : X, ∑ x : Bool, ∑ y : Bool,
      (if Bool.xor (Bool.xor (x && y) (x && u z)) (Bool.xor (y && v z) (w z)) then (-1 : ℤ) else 1))
      = 2 * ∑ z : X, (if Bool.xor (w z) (u z && v z) then (-1 : ℤ) else 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Fintype.sum_bool]
  cases he : u z <;> cases hf : v z <;> cases hg : w z <;> decide
