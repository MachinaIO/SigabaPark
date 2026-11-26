import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Common
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

theorem solution {K : Type*} [Field K] [DecidableEq K] (S : Finset K)
    {ι : Type*} [DecidableEq ι] (tests : Finset ι) (a b : ι → K)
    (hab : ∀ i ∈ tests, a i ≠ 0 ∨ b i ≠ 0) :
    (S.filter (fun t => ∃ i ∈ tests, a i * t + b i = 0)).card ≤ tests.card := by
  classical
  have hsub : S.filter (fun t => ∃ i ∈ tests, a i * t + b i = 0)
      ⊆ tests.biUnion (fun i => S.filter (fun t => a i * t + b i = 0)) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hS, i, hi, he⟩ := ht
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hS, he⟩⟩
  have hone : ∀ i ∈ tests, (S.filter (fun t => a i * t + b i = 0)).card ≤ 1 := by
    intro i hi
    rw [Finset.card_le_one]
    intro t ht t' ht'
    rw [Finset.mem_filter] at ht ht'
    have h1 : a i * (t - t') = 0 := by linear_combination ht.2 - ht'.2
    rcases mul_eq_zero.mp h1 with h | h
    · rcases hab i hi with h' | h'
      · exact absurd h h'
      · exfalso; apply h'; have := ht.2; rw [h, zero_mul, zero_add] at this; exact this
    · linear_combination h
  calc (S.filter (fun t => ∃ i ∈ tests, a i * t + b i = 0)).card
      ≤ (tests.biUnion (fun i => S.filter (fun t => a i * t + b i = 0))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ tests, (S.filter (fun t => a i * t + b i = 0)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ tests, 1 := Finset.sum_le_sum hone
    _ = tests.card := by simp
