import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

theorem solution {ι κ : Type*} (clause : κ → ℕ → Bool → Bool)
    (pad pad' : ι → ℕ → Bool → Bool) (T : ℕ → (ℕ → Bool) → Prop)
    (hT : ∀ k ℓ (x : ℕ → Bool), (∀ i, ℓ ≤ i → ∀ c, clause k i c = true) →
      (∀ i < ℓ, clause k i (x i) = true) → T ℓ x)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (d : ι) (L : ℕ) (b : Bool) (cover : ℕ → Bool → Bool)
    (hcover : (∃ e, e ≠ d ∧ cover = pad e) ∨ ∃ k, cover = clause k)
    (hcol : ∀ i < L, ∀ c, pad d i c = cover i c)
    (hLb : cover L b = true)
    (htail : ∀ i, L < i → ∀ c, cover i c = true)
    (hother : ∀ e, e ≠ d → pad' e = pad e)
    (hd : ∀ i c, ¬ (i = L ∧ c = b) → pad' d i c = pad d i c) :
    ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad' e i (x i) = true) → T ℓ x := by
  intro e ℓ x hℓ hal
  by_cases he : e = d
  · subst he
    by_cases hx : L < ℓ ∧ x L = b
    · have hcal : ∀ i < ℓ, cover i (x i) = true := by
        intro i hi
        rcases lt_trichotomy i L with h | h | h
        · rw [← hcol i h (x i), ← hd i (x i) (by rintro ⟨rfl, _⟩; omega)]
          exact hal i hi
        · subst h; rw [hx.2]; exact hLb
        · exact htail i h (x i)
      rcases hcover with ⟨e', -, rfl⟩ | ⟨k, rfl⟩
      · exact hJ e' ℓ x hℓ hcal
      · exact hT k ℓ x (fun i hi c => htail i (by omega) c) hcal
    · apply hJ e ℓ x hℓ
      intro i hi
      rw [← hd i (x i) (by rintro ⟨rfl, h⟩; exact hx ⟨hi, h⟩)]
      exact hal i hi
  · apply hJ e ℓ x hℓ
    intro i hi
    rw [← hother e he]
    exact hal i hi
