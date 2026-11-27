import Mathlib

theorem solution (lam n ell : ℕ) (hl : 128 ≤ lam) (hn : 512 ≤ n) (he : 128 ≤ ell) :
    2^32 ≤ lam * n * (2 * ell)^2 := by
  calc
    2^32 = (128:ℕ) * 512 * (2 * 128)^2 := by norm_num
    _ ≤ lam * n * (2 * ell)^2 := by gcongr
