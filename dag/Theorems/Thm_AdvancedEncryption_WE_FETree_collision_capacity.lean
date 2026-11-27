import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem AdvancedEncryption.WE.FETree.collision_capacity {S M C : Type} [Fintype S] [Fintype M] [Fintype C]
    (w : S → ℝ) (p : S → M → C → ℝ) (read : S → C → M)
    (hw : ∀ s, 0 ≤ w s) (hn : ∑ s, w s = 1)
    (hg : 3 * (Fintype.card M : ℝ) ≤ 4 * ∑ s, w s * ∑ c, p s (read s c) c)
    (hb : 512 * (∑ s, w s * ∑ c, ∑ m, (p s m c)^2) ≤ (Fintype.card M : ℝ)) :
    256 * (Fintype.card M : ℝ) ≤ (Fintype.card C : ℝ) := by
  sorry
