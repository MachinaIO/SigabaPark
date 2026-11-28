import Mathlib

theorem solution {I : Type*} [Fintype I] [DecidableEq I] (prob gap : I → ℝ) (j : I)
    (hp : ∀ i, 0 ≤ prob i) : prob j*(gap j)^2 ≤ ∑ i, prob i*(gap i)^2 := by
  exact Finset.single_le_sum (fun i _ => mul_nonneg (hp i) (sq_nonneg _)) (Finset.mem_univ j)
