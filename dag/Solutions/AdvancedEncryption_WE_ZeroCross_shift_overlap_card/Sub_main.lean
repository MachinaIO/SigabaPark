import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

theorem solution (t B : ℕ) (h : t ≤ B) :
    (Finset.range B \ Finset.Ico t (t + B)).card = t := by
  have : Finset.range B \ Finset.Ico t (t + B) = Finset.range t := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Finset.card_range]
