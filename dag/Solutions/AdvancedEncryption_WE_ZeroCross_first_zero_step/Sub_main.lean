import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

theorem solution {α : Type*} [Zero α] (f : ℕ → α) (h : ℕ) (h0 : f 0 ≠ 0) (hh : f h = 0) :
    ∃ j, j < h ∧ f j ≠ 0 ∧ f (j + 1) = 0 := by
  classical
  have hex : ∃ j, f (j + 1) = 0 := by
    cases h with
    | zero => exact absurd hh h0
    | succ k => exact ⟨k, hh⟩
  let j := Nat.find hex
  have hj : f (j + 1) = 0 := Nat.find_spec hex
  refine ⟨j, ?_, ?_, hj⟩
  · by_contra hc
    push Not at hc
    cases h with
    | zero => exact h0 hh
    | succ k => exact absurd (Nat.find_min' hex hh) (by omega)
  · intro hz
    cases hj0 : j with
    | zero => exact h0 (by simpa [hj0] using hz)
    | succ i =>
      have : f (i + 1) = 0 := by simpa [hj0] using hz
      exact absurd (Nat.find_min' hex this) (by omega)
