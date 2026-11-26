import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Common

theorem solution {V S : Type*} [Fintype V] [Fintype S] [DecidableEq S]
    (κ : V → S) (b : ℕ)
    (hb : ∀ x, (Finset.univ.filter fun y => κ y = κ x).card ≤ b) :
    Fintype.card V ≤ b * Fintype.card S := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := κ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  calc ∑ s, (Finset.univ.filter fun y => κ y = s).card
      ≤ ∑ _s : S, b := Finset.sum_le_sum fun s _ => by
        by_cases h : ∃ x, κ x = s
        · obtain ⟨x, rfl⟩ := h; exact hb x
        · have h' : ∀ y, κ y ≠ s := fun y hy => h ⟨y, hy⟩
          simp [Finset.filter_false_of_mem (fun y _ => h' y)]
    _ = b * Fintype.card S := by simp [mul_comm]
