import Mathlib

set_option maxRecDepth 8192

theorem solution (ys : List ℕ) (k : ℕ) (hn : ys.length = k)
    (hw : ys.sum + 1 = 128 + k) :
    31744 ≤ (ys.map (fun y ↦ 2 ^ y)).sum + 2 ^ k := by
  have line (a n : ℕ) : (n + 1) * 2 ^ a ≤ 2 ^ n + a * 2 ^ a := by
    by_cases h : n < a
    · have h' := Nat.mul_le_mul_right (2 ^ a) (show n + 1 ≤ a by omega)
      exact h'.trans (Nat.le_add_left _ _)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show a ≤ n by omega)
      have hj : j + 1 ≤ 2 ^ j := by
        induction j with
        | zero => decide
        | succ j ih =>
          rw [pow_succ]
          omega
      rw [pow_add]
      nlinarith [Nat.mul_le_mul_left (2 ^ a) hj]
  have sumline (xs : List ℕ) :
      (xs.sum + xs.length) * 1024 ≤ (xs.map (fun y ↦ 2 ^ y)).sum + xs.length * 10240 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have h := line 10 x
      norm_num at h
      simp only [List.sum_cons, List.length_cons, List.map_cons]
      omega
  have h₁ := sumline ys
  have h₂ := line 13 k
  norm_num at h₂
  omega
