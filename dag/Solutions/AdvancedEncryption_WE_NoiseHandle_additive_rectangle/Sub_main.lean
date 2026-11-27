import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

theorem solution {n : ℕ} {M : Type*} [AddCommGroup M] (f : Fin n → Bool → M)
    (w w' u u' : Fin n → Bool)
    (h : ∀ i, (u i = w i ∧ u' i = w' i) ∨ (u i = w' i ∧ u' i = w i)) :
    (∑ i, f i (w i)) + ∑ i, f i (w' i) = (∑ i, f i (u i)) + ∑ i, f i (u' i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  exact add_comm _ _
