import Mathlib

open scoped BigOperators

theorem solution {ι κ V : Type} [Fintype ι] [Fintype κ] [AddCommGroup V]
    (r : ι → V →+ V) (a : ι → κ → V) (h : ∀ i, r i (∑ j, a i j) = 0) :
    ∑ i, ∑ j, (a i j - r i (a i j)) = ∑ i, ∑ j, a i j := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_sub_distrib, ← map_sum, h, sub_zero]
