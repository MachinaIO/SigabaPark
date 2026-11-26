import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Common

theorem solution {μ : Type*} (q : ℕ) [NeZero q] (b ℓ : μ → ZMod q) (z : μ → ℤ)
    (hb : ∀ j, b j = ℓ j + (z j : ZMod q)) (hz : ∀ j, 2 * |z j| < q) :
    ∀ j, (b j - ℓ j).valMinAbs = z j := by
  intro j
  rw [hb j, add_sub_cancel_left, ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · have := hz j
    have h1 : -|z j| ≤ z j := neg_abs_le _
    linarith
  · have := hz j
    have h1 : z j ≤ |z j| := le_abs_self _
    linarith
