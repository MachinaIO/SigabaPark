import Mathlib

theorem solution {R : Type*} [AddCommGroup R] (base hidden target correction : R)
    (ht : target = base - hidden) :
    base - (hidden + correction) = target - correction := by
  rw [ht]
  abel
