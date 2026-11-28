import Mathlib

theorem solution {K P L : Type} [CommSemiring K] [Fintype P] [Fintype L] (a b : L → P → K) (c : P → K)
    (u : P → K) :
    (∑ i, u i * c i) + (∑ l, (∑ i, u i * a l i) * (∑ j, u j * b l j)) =
    (∑ i, u i * c i) + ∑ i, ∑ j, (u i * u j) * (∑ l, a l i * b l j) := by
  classical
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring
