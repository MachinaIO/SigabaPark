import Mathlib

open scoped BigOperators

theorem solution {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (C : A → B → ℝ) (N : ℝ) (row : ∀ a, ∑ b, C a b = N) :
    (∑ a, ∑ b, (C a b - N / Fintype.card B)^2) =
    (∑ a, ∑ b, (C a b)^2) - (Fintype.card A : ℝ)*N^2/Fintype.card B := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have inner (a : A) : (∑ b, (C a b - N / Fintype.card B)^2) =
      (∑ b, (C a b)^2) - N^2/Fintype.card B := by
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, row, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  simp_rw [inner,Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring
