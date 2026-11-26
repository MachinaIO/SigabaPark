import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

theorem solution {n : ℕ} (p z : Fin n → Bool) (l : ℕ) :
    (¬ ∀ i : Fin n, i.val < l → z i = p i) ↔
      ∃ j : Fin n, j.val < l ∧ (∀ i : Fin n, i.val < j.val → z i = p i) ∧ z j ≠ p j := by
  constructor
  · intro h
    push Not at h
    classical
    have hex : ∃ k, ∃ i : Fin n, i.val = k ∧ i.val < l ∧ z i ≠ p i := by
      obtain ⟨i, hi, hne⟩ := h; exact ⟨i.val, i, rfl, hi, hne⟩
    obtain ⟨j, hjv, hjl, hjne⟩ := Nat.find_spec hex
    refine ⟨j, hjl, ?_, hjne⟩
    intro i hi
    by_contra hc
    have := Nat.find_min' hex ⟨i, rfl, by omega, hc⟩
    omega
  · rintro ⟨j, hjl, -, hne⟩ hall
    exact hne (hall j hjl)
