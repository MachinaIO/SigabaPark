import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.terminal_ciphertext_floor (p d : ℕ) (bits : List ℕ) (total : p + bits.sum = 128)
    (arity : bits.length = d + 1)
    (prefixBound : 2^p < (2 : ℕ)^32)
    (tables : ∀ b ∈ bits, 2^b < (2 : ℕ)^32) :
    (2 : ℕ)^32 ≤ 16^(2^d) := by sorry
