import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.Push

open Finset Polynomial

theorem AdvancedEncryption.WE.PIT.boolean_cube_single_seed {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (c : Finset ℕ → K) :
    let V := range m
    let idx := fun T : Finset ℕ ↦ ∑ i ∈ T, 2 ^ i
    let p : K[X] := ∑ T ∈ V.powerset, monomial (idx T) (c T)
    let sat := ∃ S ⊆ V, (∑ T ∈ S.powerset, c T) ≠ 0
    (¬sat → ∀ a : K, p.eval a = 0) ∧
      (sat → (univ.filter fun a : K ↦ p.eval a = 0).card ≤ 2 ^ m - 1) := by
  sorry
