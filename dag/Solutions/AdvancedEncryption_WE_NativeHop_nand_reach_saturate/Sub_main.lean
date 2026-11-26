import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

theorem solution (n g : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ j < g, a j < n + j) (hb : ∀ j < g, b j < n + j)
    (R : ℕ → Set Bool) (hin : ∀ i < n, R i = Set.univ)
    (hprop : ∀ j < g, ∀ α ∈ R (a j), ∀ β ∈ R (b j), (!(α && β)) ∈ R (n + j)) :
    ∀ w < n + g, R w = Set.univ := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h : w < n
    · exact hin w h
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < g := by omega
      have hA := ih (a j) (ha j hj) (by have := ha j hj; omega)
      have hB := ih (b j) (hb j hj) (by have := hb j hj; omega)
      have h1 := hprop j hj true (by rw [hA]; trivial) true (by rw [hB]; trivial)
      have h0 := hprop j hj false (by rw [hA]; trivial) false (by rw [hB]; trivial)
      ext v
      simp only [Set.mem_univ, iff_true]
      cases v
      · simpa using h1
      · simpa using h0
