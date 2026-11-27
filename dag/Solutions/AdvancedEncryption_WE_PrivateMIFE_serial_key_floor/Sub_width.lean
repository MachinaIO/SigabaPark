import Mathlib

theorem solution (p : ℕ) (bits : List ℕ) (total : p + bits.sum = 128)
    (tables : ∀ b ∈ bits, 2 ^ b < (2 : ℕ)^32) :
    (2 : ℕ)^32 ≤ 2^p * 128^bits.length := by
  have small (b : ℕ) (h : 2^b < (2 : ℕ)^32) : b ≤ 31 := by
    by_contra! hb
    have hp : (2 : ℕ)^32 ≤ 2^b := Nat.pow_le_pow_right (by decide) hb
    omega
  have aux (xs : List ℕ) (h : ∀ b ∈ xs, 2^b < (2 : ℕ)^32) :
      xs.sum ≤ 31 * xs.length := by
    induction xs with
    | nil => simp
    | cons b xs ih =>
      have hb := small b (h b (by simp))
      have ht := ih (fun j hj ↦ h j (by simp [hj]))
      simp only [List.sum_cons, List.length_cons]
      omega
  have hsum := aux bits tables
  have floor : 32 ≤ p + 7 * bits.length := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) floor
  calc
    (2 : ℕ)^32 ≤ 2^(p+7*bits.length) := hp
    _ = 2^p * 128^bits.length := by rw [pow_add, pow_mul]; norm_num
