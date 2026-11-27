import Mathlib

theorem AdvancedEncryption.WE.BitGC.seed_bank_floor (lam n ell : ℕ) (hl : 128 ≤ lam) (hn : 512 ≤ n) (he : 128 ≤ ell) :
    2^32 ≤ lam * n * (2 * ell)^2 := by sorry
