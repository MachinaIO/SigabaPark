import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.terminal_ciphertext_composition (width : ℕ → ℕ → ℕ) (w : ℕ)
    (base : ∀ s, w * s ≤ width 0 s)
    (nested : ∀ d s, width d (width d s) ≤ width (d + 1) s)
    (d s : ℕ) : w ^ (2 ^ d) * s ≤ width d s := by sorry
