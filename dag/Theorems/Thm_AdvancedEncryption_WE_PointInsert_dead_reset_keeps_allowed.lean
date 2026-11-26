import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

/-- **Dead-level resets keep pads on allowed prefixes (note `pq-we-point-insertion-frontier`, §4).** If pad `d` has both entries `0` at level `L` and only its entries after `L` change (the dead-slot move of #111 §4), every pad is still alive only on allowed prefixes. -/
theorem AdvancedEncryption.WE.PointInsert.dead_reset_keeps_allowed {ι : Type*} (pad pad' : ι → ℕ → Bool → Bool)
    (T : ℕ → (ℕ → Bool) → Prop)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (d : ι) (L : ℕ) (hdead : ∀ c, pad d L c = false)
    (hother : ∀ e, e ≠ d → pad' e = pad e)
    (hd : ∀ i c, i ≤ L → pad' d i c = pad d i c) :
    ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad' e i (x i) = true) → T ℓ x := by sorry
