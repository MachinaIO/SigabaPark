import Mathlib.Tactic

theorem solution {I J : Type*} [Fintype I] [Fintype J]
    (A : J → I → ZMod 2) (d z : I → ZMod 2) (s : J → ZMod 2)
    (hd : ∀ j, (∑ i, d i * A j i) = 0) :
    (∑ i, d i * ((∑ j, A j i * s j) + z i)) = ∑ i, d i * z i := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hd, zero_mul, Finset.sum_const_zero, zero_add]
