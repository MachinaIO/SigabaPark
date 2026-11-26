import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

/-- **A vanishing reading has a first zero step.** If a sequence of readings `f 0, f 1, …` starts
non-zero and is zero at step `h`, then some `j < h` has `f j ≠ 0` and `f (j + 1) = 0`. Applied to
the reading `e Ŝ_{z≤j} A_j` of a GGH15 slot along a string `z` on which the pad vanishes, it
gives a non-zero row combination with a zero child at level `j + 1`. So every pad that vanishes
somewhere, in any program and any row basis, has a zero entry to cross
(note `pq-we-zero-entry-crossing`, §6). -/
theorem AdvancedEncryption.WE.ZeroCross.first_zero_step {α : Type*} [Zero α] (f : ℕ → α) (h : ℕ) (h0 : f 0 ≠ 0) (hh : f h = 0) :
    ∃ j, j < h ∧ f j ≠ 0 ∧ f (j + 1) = 0 := by sorry
