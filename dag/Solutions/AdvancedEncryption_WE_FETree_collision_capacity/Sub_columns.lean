import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution {S M C : Type} [Fintype S] [Fintype M] [Fintype C]
    (w : S → ℝ) (p : S → M → C → ℝ) (read : S → C → M)
    (hw : ∀ s, 0 ≤ w s) (hn : ∑ s, w s = 1)
    (hg : 3 * (Fintype.card M : ℝ) ≤ 4 * ∑ s, w s * ∑ c, p s (read s c) c)
    (hb : 512 * (∑ s, w s * ∑ c, ∑ m, (p s m c)^2) ≤ (Fintype.card M : ℝ)) :
    256 * (Fintype.card M : ℝ) ≤ (Fintype.card C : ℝ) := by
  classical
  let G := fun s => ∑ c, p s (read s c) c
  let B := fun s => ∑ c, ∑ m, (p s m c)^2
  have hrow (s : S) (c : C) : 512 * p s (read s c) c ≤
      65536 * (∑ m, (p s m c)^2) + 1 := by
    have h := Finset.single_le_sum (f := fun m => (p s m c)^2)
      (fun m _ => sq_nonneg (p s m c)) (Finset.mem_univ (read s c))
    nlinarith [sq_nonneg (256 * p s (read s c) c - 1)]
  have hs (s : S) : 512 * G s ≤ 65536 * B s + (Fintype.card C : ℝ) := by
    simpa [G, B, Finset.mul_sum, Finset.sum_add_distrib] using
      (Finset.sum_le_sum (s := Finset.univ) (fun c _ => hrow s c))
  have ht : 512 * (∑ s, w s * G s) ≤
      65536 * (∑ s, w s * B s) + (Fintype.card C : ℝ) := calc
    _ = ∑ s, w s * (512 * G s) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    _ ≤ ∑ s, w s * (65536 * B s + (Fintype.card C : ℝ)) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hs s) (hw s))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hn, one_mul]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun s _ => by ring)
  change 3 * (Fintype.card M : ℝ) ≤ 4 * ∑ s, w s * G s at hg
  change 512 * (∑ s, w s * B s) ≤ (Fintype.card M : ℝ) at hb
  linarith
