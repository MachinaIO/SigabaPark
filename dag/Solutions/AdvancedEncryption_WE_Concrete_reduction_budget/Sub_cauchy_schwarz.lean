import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

theorem solution (L P : ℕ) (ε : ℕ → ℝ)
    (adv c T : ℝ) (hc : 1 ≤ c) (hT : 0 ≤ T) (hadv0 : 0 ≤ adv)
    (hadv : adv ≤ ∑ i ∈ Finset.range L, ε i)
    (hhop : ∀ i < L, (2 : ℝ) ^ P * ε i ^ 2 ≤ c + T) :
    (2 : ℝ) ^ P * adv ^ 2 ≤ (L : ℝ) ^ 2 * (1 + T) * c := by
  have hcs : (∑ i ∈ Finset.range L, ε i) ^ 2 ≤
      (L : ℝ) * ∑ i ∈ Finset.range L, ε i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range L) (f := ε)
  have hsq : adv ^ 2 ≤ (∑ i ∈ Finset.range L, ε i) ^ 2 := by
    exact pow_le_pow_left₀ hadv0 hadv 2
  have hsum : (2 : ℝ) ^ P * ∑ i ∈ Finset.range L, ε i ^ 2 ≤ (L : ℝ) * (c + T) := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range L, (2 : ℝ) ^ P * ε i ^ 2
        ≤ ∑ _i ∈ Finset.range L, (c + T) :=
          Finset.sum_le_sum fun i hi => hhop i (Finset.mem_range.mp hi)
      _ = (L : ℝ) * (c + T) := by simp; ring
  have h2P : (0 : ℝ) ≤ 2 ^ P := by positivity
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hcT : c + T ≤ (1 + T) * c := by nlinarith
  calc (2 : ℝ) ^ P * adv ^ 2
      ≤ 2 ^ P * ((L : ℝ) * ∑ i ∈ Finset.range L, ε i ^ 2) :=
        mul_le_mul_of_nonneg_left (hsq.trans hcs) h2P
    _ = (L : ℝ) * (2 ^ P * ∑ i ∈ Finset.range L, ε i ^ 2) := by ring
    _ ≤ (L : ℝ) * ((L : ℝ) * (c + T)) := mul_le_mul_of_nonneg_left hsum hL
    _ ≤ (L : ℝ) * ((L : ℝ) * ((1 + T) * c)) := by gcongr
    _ = (L : ℝ) ^ 2 * (1 + T) * c := by ring
