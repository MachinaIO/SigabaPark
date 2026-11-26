import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

/-- **Copies keep pads on allowed prefixes (note `pq-we-point-insertion-frontier`, §5).** The symmetric co-located copy turns pad `d` into a copy of its partner (a pad, or a clause in the shared-block variant). If the copied program is alive only on allowed prefixes, so is every pad afterwards. -/
theorem AdvancedEncryption.WE.PointInsert.copy_keeps_allowed {ι : Type*} (pad pad' : ι → ℕ → Bool → Bool)
    (T : ℕ → (ℕ → Bool) → Prop)
    (hJ : ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad e i (x i) = true) → T ℓ x)
    (d : ι) (src : ℕ → Bool → Bool)
    (hsrc : ∀ ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, src i (x i) = true) → T ℓ x)
    (hother : ∀ e, e ≠ d → pad' e = pad e) (hd : pad' d = src) :
    ∀ e ℓ (x : ℕ → Bool), 1 ≤ ℓ → (∀ i < ℓ, pad' e i (x i) = true) → T ℓ x := by sorry
