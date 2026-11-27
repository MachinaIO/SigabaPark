import Mathlib

theorem solution (p d : ℕ) (bits : List ℕ) (total : p + bits.sum = 128)
    (arity : bits.length = d + 1)
    (prefixBound : 2^p < (2 : ℕ)^32)
    (tables : ∀ b ∈ bits, 2^b < (2 : ℕ)^32) :
    (2 : ℕ)^32 ≤ 16^(2^d) := by
  have narrow (b : ℕ) (hb : 2^b < (2 : ℕ)^32) : b ≤ 31 := by
    by_contra! hh
    have hz := Nat.pow_le_pow_right (n := 2) (by decide) (show 32 ≤ b by omega)
    omega
  have sumBound (l : List ℕ) (h : ∀ b ∈ l, 2^b < (2 : ℕ)^32) :
      l.sum ≤ 31*l.length := by
    induction l with
    | nil => simp
    | cons b l ih =>
      have hb := narrow b (h b (by simp))
      have ht := ih (fun j hj ↦ h j (by simp [hj]))
      simp only [List.sum_cons, List.length_cons]
      omega
  have h1 := narrow p prefixBound
  have h2 := sumBound bits tables
  have hd : 3 ≤ d := by omega
  have he : 8 ≤ 2^d := Nat.pow_le_pow_right (n := 2) (by decide) hd
  calc
    (2 : ℕ)^32 = 16^8 := by decide
    _ ≤ _ := Nat.pow_le_pow_right (n := 16) (by decide) he
