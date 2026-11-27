import Mathlib

theorem solution (J : ℕ) (h : 4 * 16384 * 128 * 280 + J * ((3 * 128+1)*280+1) ≤ 2^32) :
    J ≤ 18053 ∧ J + 15000 + 15 + 2050 + 540 + 1 ≤ 279 * 128 ∧
    (65537 : ℕ)^128 ≤ (2^41)^50 := by
  have hj : J ≤ 18053 := by omega
  exact ⟨hj, by omega, by norm_num⟩
