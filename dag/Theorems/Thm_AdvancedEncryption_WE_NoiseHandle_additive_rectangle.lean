import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

theorem AdvancedEncryption.WE.NoiseHandle.additive_rectangle {n : ℕ} {M : Type*} [AddCommGroup M] (f : Fin n → Bool → M)
    (w w' u u' : Fin n → Bool)
    (h : ∀ i, (u i = w i ∧ u' i = w' i) ∨ (u i = w' i ∧ u' i = w i)) :
    (∑ i, f i (w i)) + ∑ i, f i (w' i) = (∑ i, f i (u i)) + ∑ i, f i (u' i) := by sorry
