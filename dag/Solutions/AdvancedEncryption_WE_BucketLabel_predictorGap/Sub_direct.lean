import Definitions.Def_BucketLabel
open BucketLabel
theorem solution (r0 r1 u0 u1 δ : ℚ)
    (hIdeal : u0 = u1) (h : |(r0-r1)-(u0-u1)| ≤ 2*δ) :
    |(r0 + (1-r1))/2 - 1/2| ≤ δ := by
  rw [hIdeal, sub_self, sub_zero] at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1,h.2]
