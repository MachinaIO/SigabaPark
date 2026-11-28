import Mathlib

theorem solution {T : Type*} [AddCommMonoid T] (d : T) (k : ℕ) (h : 2 • d = 0) :
    (k*2+1) • d = d := by
  rw [Nat.mul_comm k 2, add_nsmul, mul_nsmul, h]
  simp
