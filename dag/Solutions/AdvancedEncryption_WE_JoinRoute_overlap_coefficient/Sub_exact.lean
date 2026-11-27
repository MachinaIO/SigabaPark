import Mathlib

theorem solution {T : Type} [DecidableEq T] (P Q : Finset T) :
    (∑ i ∈ P, ∑ j ∈ Q, if i = j then (1:ℕ) else 0) = (P ∩ Q).card := by
  classical
  simp only [Finset.sum_ite_eq]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  congr 1
