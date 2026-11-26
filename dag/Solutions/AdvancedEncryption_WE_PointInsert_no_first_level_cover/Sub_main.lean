import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

theorem solution {ι κ : Type*} (clause : κ → ℕ → Bool → Bool)
    (pad : ι → ℕ → Bool → Bool) (T : ℕ → (ℕ → Bool) → Prop)
    (hT : ∀ k ℓ (x : ℕ → Bool), (∀ i, ℓ ≤ i → ∀ c, clause k i c = true) →
      (∀ i < ℓ, clause k i (x i) = true) → T ℓ x)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (b : Bool) (x : ℕ → Bool) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hx0 : x 0 = b) (hx : ¬ T ℓ x)
    (cover : ℕ → Bool → Bool)
    (hcover : (∃ e, cover = pad e) ∨ ∃ k, cover = clause k)
    (h0 : cover 0 b = true) (htail : ∀ i, 0 < i → ∀ c, cover i c = true) : False := by
  have hcal : ∀ i < ℓ, cover i (x i) = true := by
    intro i _
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; rw [hx0]; exact h0
    · exact htail i h (x i)
  rcases hcover with ⟨e, rfl⟩ | ⟨k, rfl⟩
  · exact hx (hJ e ℓ x hℓ hcal)
  · exact hx (hT k ℓ x (fun i hi c => htail i (by omega) c) hcal)
