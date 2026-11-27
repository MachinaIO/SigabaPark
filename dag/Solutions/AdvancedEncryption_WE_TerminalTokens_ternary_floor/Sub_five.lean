import Mathlib

theorem solution (front : List ℕ) (b : ℕ)
    (total : front.sum + b = 128)
    (small : ∀ a ∈ front, a ≤ 25) (hb : b ≤ 25) :
    2^32 ≤ 64 * (front.map (fun a => 2^a)).sum +
      2^b * 3^(2^(front.length-1)-1) := by
  have bound (l : List ℕ) (hs : ∀ a ∈ l, a ≤ 25) : l.sum ≤ 25*l.length := by
    induction l with
    | nil => simp
    | cons x l ih =>
      have hx := hs x (by simp)
      have h := ih (fun a ha => hs a (by simp [ha]))
      simp only [List.sum_cons, List.length_cons]
      omega
  have tangent (a : ℕ) : 8388608*a ≤ 2^a + 184549376 := by
    by_cases hs : a < 23
    · interval_cases a <;> decide
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show 23 ≤ a by omega)
      induction j with
      | zero => decide
      | succ j ih =>
        have h : 2^23 ≤ 2^(23+j) := Nat.pow_le_pow_right (by decide) (by omega)
        rw [show 23+(j+1)=(23+j)+1 by omega,pow_succ]
        omega
  have grouped (l : List ℕ) :
      8388608*l.sum ≤ (l.map (fun a => 2^a)).sum + 184549376*l.length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have h := tangent a
      simp only [List.sum_cons, List.map_cons, List.length_cons]
      omega
  have hf := bound front small
  have hp : 1 ≤ 2^b := Nat.one_le_pow _ _ (by decide)
  by_cases sh : front.length ≤ 5
  · have len : front.length = 5 := by omega
    rw [len]
    by_cases low : b ≤ 8
    · have h := grouped front
      rw [len] at h
      omega
    · have h : 2^9 ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num
      omega
  · have hd : 2^5 ≤ 2^(front.length-1) := Nat.pow_le_pow_right (by decide) (by omega)
    have he : 3^31 ≤ 3^(2^(front.length-1)-1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h := Nat.mul_le_mul hp he
    omega
