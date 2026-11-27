import Mathlib

theorem solution (groups : List ℕ) (total : groups.sum = 128) (few : groups.length ≤ 16)
    (N width field : ℕ) (unitCost : 2 ^ 19 ≤ N * width * field) :
    (2 : ℕ) ^ 32 ≤ 2 * (N * width * field) * (groups.map fun e ↦ 2 ^ e).sum := by
  have tangent (e : ℕ) : 256 * e ≤ 2 ^ e + 1792 := by
    by_cases hs : e < 8
    · interval_cases e <;> decide
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 8 ≤ e by omega)
      induction j with
      | zero => decide
      | succ j ih =>
        have hg : 256 ≤ 2 ^ (8+j) := Nat.pow_le_pow_right (n := 2) (by decide) (show 8 ≤ 8+j by omega)
        rw [show 8 + (j + 1) = (8+j)+1 by omega, pow_succ]
        omega
  have summed (xs : List ℕ) :
      256 * xs.sum ≤ (xs.map fun e ↦ 2 ^ e).sum + 1792 * xs.length := by
    induction xs with
    | nil => simp
    | cons e xs ih =>
      have h := tangent e
      simp only [List.sum_cons, List.map_cons, List.length_cons]
      omega
  have hs := summed groups
  have bound : 4096 ≤ (groups.map fun e ↦ 2 ^ e).sum := by omega
  calc
    (2 : ℕ)^32 = 2 * 2^19 * 4096 := by decide
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left 2 unitCost) bound
