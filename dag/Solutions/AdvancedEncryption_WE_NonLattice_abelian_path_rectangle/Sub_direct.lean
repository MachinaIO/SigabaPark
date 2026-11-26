import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

theorem solution {G : Type*} [AddCommGroup G] {L n : ℕ}
    (var : Fin L → Fin n) (f : Fin L → Bool → G) (w : Fin n → Bool) (i k : Fin n) (hik : i ≠ k) :
    (∑ j, f j (Function.update (Function.update w i false) k false (var j))) +
      ∑ j, f j (Function.update (Function.update w i true) k true (var j))
    = (∑ j, f j (Function.update (Function.update w i false) k true (var j))) +
      ∑ j, f j (Function.update (Function.update w i true) k false (var j)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hk : var j = k
  · rw [hk]; simp only [Function.update_self]; abel
  · by_cases hi : var j = i
    · rw [hi]; simp only [Function.update_of_ne hik, Function.update_self]
    · simp only [Function.update_of_ne hk, Function.update_of_ne hi]
