import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

theorem solution (f : ℕ → ℝ) (K ε : ℝ) (hK : 0 ≤ K) (T : ℕ)
    (hhop : ∀ i < T, f i ≤ K * f (i + 1) + ε) :
    f 0 ≤ K ^ T * f T + ε * ∑ i ∈ Finset.range T, K ^ i := by
  have : ∀ t ≤ T, f 0 ≤ K ^ t * f t + ε * ∑ i ∈ Finset.range t, K ^ i := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := hhop t (by omega)
      have hp : 0 ≤ K ^ t := pow_nonneg hK t
      have h3 : K ^ t * f t ≤ K ^ t * (K * f (t + 1) + ε) := mul_le_mul_of_nonneg_left h2 hp
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [h1, h3]
  exact this T le_rfl
