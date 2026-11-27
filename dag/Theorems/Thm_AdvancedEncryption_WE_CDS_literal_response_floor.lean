import Mathlib

theorem AdvancedEncryption.WE.CDS.literal_response_floor (b m : ℕ) (hm : 256 * b ≤ m)
    (hq : 128 ^ 3 * (8 * m + 4) ≤ 2 ^ b) :
    2 ^ 32 < 128 ^ 2 * (m - 1) * b := by sorry
