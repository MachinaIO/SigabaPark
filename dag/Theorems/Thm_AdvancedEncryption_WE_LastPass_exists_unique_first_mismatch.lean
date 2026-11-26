import Mathlib.Data.Fintype.Basic

/-- **Equality cubes.** Every `y ≠ t` in `{0,1}^n` has a unique first mismatch position `j`
(`y_i = t_i` for `i < j`, `y_j ≠ t_j`). So the orphans `(y, …, t)` of the consistent string `t`
split into the `n` cubes `C_j = t_{<j} · ¬t_j · {0,1}^{n−j−1}`, and the strings of `C_j` falsify
the equality clause at position `j`. -/
theorem AdvancedEncryption.WE.LastPass.exists_unique_first_mismatch {n : ℕ} (y t : Fin n → Bool)
    (h : y ≠ t) : ∃! j : Fin n, (∀ i : Fin n, i < j → y i = t i) ∧ y j ≠ t j := by sorry
