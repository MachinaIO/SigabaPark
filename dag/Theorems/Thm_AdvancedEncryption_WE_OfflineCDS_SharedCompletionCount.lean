import Mathlib

theorem AdvancedEncryption.WE.OfflineCDS.SharedCompletionCount {Tape : Type*} [DecidableEq Tape] (u : ℕ) (good : (Fin u → Bool) → Finset Tape)
    (n : ℕ) (bound : ∀ y, (good y).card ≤ n) :
    (Finset.univ.biUnion good).card ≤ 2^u*n := by sorry
