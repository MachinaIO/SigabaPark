import Mathlib

theorem AdvancedEncryption.WE.LockHeader.completion_budget (s q : ℕ)
    (hclock : q < 2 ^ 32)
    (hcorrect : (2 ^ 127 - 1) * 2 ^ s ≤ 2 ^ 127 * q) : s ≤ 31 := by sorry
