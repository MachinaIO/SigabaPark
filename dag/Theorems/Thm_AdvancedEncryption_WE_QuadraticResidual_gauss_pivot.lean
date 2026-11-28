import Mathlib

theorem AdvancedEncryption.WE.QuadraticResidual.gauss_pivot {X : Type} [Fintype X] (u v w : X → Bool) :
    (∑ z : X, ∑ x : Bool, ∑ y : Bool,
      (if Bool.xor (Bool.xor (x && y) (x && u z)) (Bool.xor (y && v z) (w z)) then (-1 : ℤ) else 1))
      = 2 * ∑ z : X, (if Bool.xor (w z) (u z && v z) then (-1 : ℤ) else 1) := by
  sorry
