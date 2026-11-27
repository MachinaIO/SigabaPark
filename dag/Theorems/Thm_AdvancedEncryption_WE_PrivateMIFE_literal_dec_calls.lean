import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.literal_dec_calls (D : ℕ → ℕ) (hbase : D 0 = 1)
    (hstep : ∀ j, D (j + 1) = 2 * D j + 1) (j : ℕ) :
    D j + 1 = 2 ^ (j + 1) := by sorry
