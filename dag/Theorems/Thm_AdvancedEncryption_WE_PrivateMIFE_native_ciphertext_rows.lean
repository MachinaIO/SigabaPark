import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.native_ciphertext_rows (groups : List ℕ) (total : groups.sum = 128) (few : groups.length ≤ 16)
    (N width field : ℕ) (unitCost : 2 ^ 19 ≤ N * width * field) :
    (2 : ℕ) ^ 32 ≤ 2 * (N * width * field) * (groups.map fun e ↦ 2 ^ e).sum := by sorry
