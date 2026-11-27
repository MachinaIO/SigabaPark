import Mathlib.Tactic

theorem solution (levels n m width outputs : ℕ)
    (hn : (12 * levels) ^ 2 ≤ n) (hm : 5 * n ≤ m)
    (hw : 12 * levels ≤ width) (hr : n * m * (12 * levels) ≤ outputs) :
    25 * (12 * levels) ^ 10 ≤ outputs * (n * m * width) ∧
    (1 ≤ levels → 3748295401 < 4 * (outputs * (n * m * width))) ∧
    (62 ≤ levels → 2 ^ 100 < outputs * (n * m * width)) ∧
    (256 ≤ levels → 2 ^ 120 < outputs * (n * m * width)) := by
  let t := 12 * levels
  have hm' : 5 * t ^ 2 ≤ m := (Nat.mul_le_mul_left 5 hn).trans hm
  have hs : 5 * t ^ 5 ≤ n * m * t := calc
    5 * t ^ 5 = t ^ 2 * (5 * t ^ 2) * t := by ring
    _ ≤ n * m * t := Nat.mul_le_mul_right t (Nat.mul_le_mul hn hm')
  have hb : 25 * t ^ 10 ≤ outputs * (n * m * width) := calc
    25 * t ^ 10 = (5 * t ^ 5) * (5 * t ^ 5) := by ring
    _ ≤ _ := Nat.mul_le_mul (hs.trans hr) (hs.trans (Nat.mul_le_mul_left _ hw))
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro h
    have ht : 12 ≤ t := by dsimp [t]; omega
    have hmin : 25 * 12 ^ 10 ≤ outputs * (n * m * width) :=
      (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left ht 10)).trans hb
    omega
  · intro h
    have ht : 744 ≤ t := by dsimp [t]; omega
    exact lt_of_lt_of_le (by decide : 2 ^ 100 < 25 * 744 ^ 10)
      ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left ht 10)).trans hb)
  · intro h
    have ht : 3072 ≤ t := by dsimp [t]; omega
    exact lt_of_lt_of_le (by decide : 2 ^ 120 < 25 * 3072 ^ 10)
      ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left ht 10)).trans hb)
