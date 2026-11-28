import Mathlib

theorem solution (W e : ℤ) (he : 0 ≤ e) (hb : e ≤ 2*W+1) :
    ((Finset.Icc (-W) W) ∩ Finset.Icc (-W+e) (W+e)).card =
      (2*W+1-e).toNat := by
  have h : ((Finset.Icc (-W) W) ∩ Finset.Icc (-W+e) (W+e)) =
      Finset.Icc (-W+e) W := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_Icc]
    omega
  rw [h, Int.card_Icc]
  congr 1
  omega
