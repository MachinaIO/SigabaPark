import Mathlib

theorem AdvancedEncryption.WE.AffinePhase.guarded_phase (z e h : ℤ) (hh : 2 < h) (he : -1 ≤ e ∧ e ≤ 1)
    (guard : 0 < (z + e) % h ∧ (z + e) % h < h-1) :
    z / h = (z + e) / h := by sorry
