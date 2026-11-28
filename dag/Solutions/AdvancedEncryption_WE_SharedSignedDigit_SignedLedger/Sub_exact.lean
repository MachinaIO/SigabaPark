import Mathlib

theorem solution (n : ℕ) (Q β : ℤ) (a t : Fin n → ℤ) :
    2*Q*β + ∑ i, (1-2*t i)*(Q+a i) =
      (∑ i, (Q+a i)) - 2*(∑ i, t i*a i) + 2*Q*(β-∑ i, t i) := by
  simp only [sub_mul, one_mul, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [show ∀ i, 2 * t i * Q = (2*Q) * t i by intro i; ring,
    show ∀ i, 2 * t i * a i = 2 * (t i * a i) by intro i; ring]
  simp only [← Finset.mul_sum]
  ring
