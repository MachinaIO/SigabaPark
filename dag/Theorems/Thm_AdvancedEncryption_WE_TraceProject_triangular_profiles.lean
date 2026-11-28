import Mathlib

theorem AdvancedEncryption.WE.TraceProject.triangular_profiles {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (compat : Fin n → Fin n → Prop) (ord : ∀ i j, compat i j → i ≤ j)
    (support : ∀ i j, M i j ≠ 0 → compat i j) (diag : ∀ i, M i i = 1) :
    M.rank = n := by
  sorry
