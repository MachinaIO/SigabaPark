import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

theorem solution {ι : Type*} (pad pad' : ι → ℕ → Bool → Bool)
    (T : ℕ → (ℕ → Bool) → Prop)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (d : ι) (src : ℕ → Bool → Bool)
    (hsrc : ∀ ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, src i (x i) = true) → T ℓ x)
    (hother : ∀ e, e ≠ d → pad' e = pad e) (hd : pad' d = src) :
    ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad' e i (x i) = true) → T ℓ x := by
  intro e ℓ x hℓ hal
  by_cases he : e = d
  · subst he
    rw [hd] at hal
    exact hsrc ℓ x hℓ hal
  · apply hJ e ℓ x hℓ
    intro i hi
    rw [← hother e he]
    exact hal i hi
