import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

theorem solution {ι : Type*} (pad pad' : ι → ℕ → Bool → Bool)
    (T : ℕ → (ℕ → Bool) → Prop)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (d : ι) (L : ℕ) (hdead : ∀ c, pad d L c = false)
    (hother : ∀ e, e ≠ d → pad' e = pad e)
    (hd : ∀ i c, i ≤ L → pad' d i c = pad d i c) :
    ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad' e i (x i) = true) → T ℓ x := by
  intro e ℓ x hℓ hal
  by_cases he : e = d
  · subst he
    by_cases hL : L < ℓ
    · have h1 := hal L hL
      rw [hd L (x L) le_rfl, hdead] at h1
      exact absurd h1 (by simp)
    · apply hJ e ℓ x hℓ
      intro i hi
      rw [← hd i (x i) (by omega)]
      exact hal i hi
  · apply hJ e ℓ x hℓ
    intro i hi
    rw [← hother e he]
    exact hal i hi
