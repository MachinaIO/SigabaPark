import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Choose

theorem AdvancedEncryption.WE.XWE.selector_support_cover (K : Type*) [Field K] {m n : ℕ} (S : Fin m → Finset (Fin n)) (d : ℕ) :
    (∃ A : Matrix (Fin m) (Fin n) K, A.rank ≤ d ∧
      (∀ i, ∃ j, A i j ≠ 0) ∧ ∀ i j, A i j ≠ 0 → j ∈ S i) ↔
    ∃ C : Finset (Fin n), C.card ≤ d ∧ ∀ i, ∃ j ∈ C, j ∈ S i := by
  sorry
