import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Tactic.Common
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution (k : ℕ) (d : ℤ)
    (h : ∀ b < k, ∃ r : ℤ, |r| < 2 ^ (k - 1) ∧ (2 : ℤ) ^ k ∣ 2 ^ b * d - r) :
    (2 : ℤ) ^ k ∣ d := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    -- step 1: `d` is even, from the hypothesis at `b = k`
    obtain ⟨r, hr, m, hm⟩ := h k (Nat.lt_succ_self k)
    simp only [Nat.add_sub_cancel] at hr
    have hpos : (0 : ℤ) < 2 ^ k := by positivity
    have heven : (2 : ℤ) ∣ d := by
      by_contra hodd
      obtain ⟨t, ht⟩ : ∃ t, d = 2 * t + 1 := by
        rcases Int.even_or_odd d with ⟨t, ht⟩ | ⟨t, ht⟩
        · exact absurd ⟨t, by omega⟩ hodd
        · exact ⟨t, ht⟩
      -- r = 2^k (1 + 2 t - 2 m)
      have hr' : r = 2 ^ k * (1 + 2 * t - 2 * m) := by
        rw [pow_succ] at hm; rw [ht] at hm; linarith
      have h1 : (1 : ℤ) ≤ |1 + 2 * t - 2 * m| := by
        rcases le_or_gt 0 (1 + 2 * t - 2 * m) with h0 | h0
        · rw [abs_of_nonneg h0]; omega
        · rw [abs_of_neg h0]; omega
      have : (2 : ℤ) ^ k ≤ |r| := by
        rw [hr', abs_mul, abs_of_pos hpos]; nlinarith
      linarith
    obtain ⟨d', rfl⟩ := heven
    -- step 2: the hypotheses at `b < k` descend to `d'`
    have h' : ∀ b < k, ∃ r : ℤ, |r| < 2 ^ (k - 1) ∧ (2 : ℤ) ^ k ∣ 2 ^ b * d' - r := by
      intro b hb
      obtain ⟨r, hr, m, hm⟩ := h b (by omega)
      simp only [Nat.add_sub_cancel] at hr
      -- r = 2^(b+1) d' - 2^(k+1) m is even
      have hr2 : r = 2 * (2 ^ b * d' - 2 ^ k * m) := by
        rw [pow_succ] at hm; linarith
      refine ⟨2 ^ b * d' - 2 ^ k * m, ?_, ⟨m, by ring⟩⟩
      have habs : |r| = 2 * |2 ^ b * d' - 2 ^ k * m| := by
        rw [hr2, abs_mul]; norm_num
      rcases k with _ | k
      · omega
      · simp only [Nat.add_sub_cancel]
        rw [pow_succ] at hr; linarith
    obtain ⟨c, hc⟩ := ih d' h'
    exact ⟨c, by rw [hc, pow_succ]; ring⟩
