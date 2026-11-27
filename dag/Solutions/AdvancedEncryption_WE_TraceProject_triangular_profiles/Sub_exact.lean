import Mathlib

theorem solution {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (compat : Fin n → Fin n → Prop) (ord : ∀ i j, compat i j → i ≤ j)
    (support : ∀ i j, M i j ≠ 0 → compat i j) (diag : ∀ i, M i i = 1) :
    M.rank = n := by
  have up : M.IsUpperTriangular := by
    intro i j h
    by_contra hn
    exact (not_le_of_gt h) (ord i j (support i j hn))
  have det : M.det = 1 := by rw [Matrix.det_of_isUpperTriangular up]; simp [diag]
  simpa using Matrix.rank_of_det_ne_zero (A := M) (by rw [det]; exact one_ne_zero)
