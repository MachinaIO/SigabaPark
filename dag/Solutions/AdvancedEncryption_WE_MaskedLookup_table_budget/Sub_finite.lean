import Mathlib
open scoped BigOperators

theorem solution (front : List ℕ) (b : ℕ)
    (total : front.sum+b=128) (sizes : ∀ k ∈ front, k ≤ 25) (last : b ≤ 25) :
    (2:ℕ)^32 ≤ 2^b * 4^(2^(front.length-1)-1) := by
  have sum_bound (xs : List ℕ) (h : ∀ k ∈ xs, k ≤ 25) : xs.sum ≤ 25*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun k hk ↦ h k (by simp [hk]))
      simp only [List.sum_cons, List.length_cons]
      omega
  have hs := sum_bound front sizes
  by_cases h : front.length ≤ 5
  · have len : front.length = 5 := by omega
    have hb : 3 ≤ b := by omega
    have hn : (2:ℕ)^3 ≤ 2^b := Nat.pow_le_pow_right (by decide) hb
    rw [len]
    norm_num at *
    omega
  · have hd : 5 ≤ front.length-1 := by omega
    have ht : (2:ℕ)^5 ≤ 2^(front.length-1) := Nat.pow_le_pow_right (by decide) hd
    have he : 31 ≤ 2^(front.length-1)-1 := by omega
    have hk : (4:ℕ)^31 ≤ 4^(2^(front.length-1)-1) := Nat.pow_le_pow_right (by decide) he
    have hp : 1 ≤ (2:ℕ)^b := Nat.succ_le_of_lt (Nat.pow_pos (by decide))
    calc
      (2:ℕ)^32 ≤ 1*4^31 := by decide
      _ ≤ _ := Nat.mul_le_mul hp hk
