import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.serial_key_floor (p : ℕ) (bits : List ℕ) (total : p + bits.sum = 128)
    (tables : ∀ b ∈ bits, 2 ^ b < (2 : ℕ)^32) :
    (2 : ℕ)^32 ≤ 2^p * 128^bits.length := by sorry
