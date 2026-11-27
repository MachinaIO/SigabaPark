import Mathlib

theorem AdvancedEncryption.WE.RoundedAudit.dither_pair_bijective {K : Type*} [Field K] (l r x y : K) (hxy : x ≠ y) :
    Function.Bijective (fun t : K × K ↦ (t.2 + l + t.1*x, t.2 + r + t.1*y)) := by sorry
