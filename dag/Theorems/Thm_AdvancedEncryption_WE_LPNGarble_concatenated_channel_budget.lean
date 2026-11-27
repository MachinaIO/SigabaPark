import Mathlib

theorem AdvancedEncryption.WE.LPNGarble.concatenated_channel_budget : let p : ℚ := 7159 / 50000
    let z := p * (1 - p)
    ((1-p) / (1-2*p)) *
        (126 * (Nat.choose 32 16 : ℚ) * z^16 + (Nat.choose 64 32 : ℚ) * z^32)
      < 1/4000 ∧
    2^161 * 32768 * Nat.choose 114 21 < 4000^21 := by sorry
