import Mathlib

theorem AdvancedEncryption.WE.SealedRow.pair_seed_bijection {K : Type*} [Field K] {x y : K} (h : x ≠ y) :
    Function.Bijective (fun p : K × K ↦ (p.1 * x + p.2, p.1 * y + p.2)) := by sorry
