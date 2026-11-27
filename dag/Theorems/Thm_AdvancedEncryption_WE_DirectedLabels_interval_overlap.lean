import Mathlib

theorem AdvancedEncryption.WE.DirectedLabels.interval_overlap (W e : ℤ) (he : 0 ≤ e) (hb : e ≤ 2*W+1) :
    ((Finset.Icc (-W) W) ∩ Finset.Icc (-W+e) (W+e)).card =
      (2*W+1-e).toNat := by sorry
