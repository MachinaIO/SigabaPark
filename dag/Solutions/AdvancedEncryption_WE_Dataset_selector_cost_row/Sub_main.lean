import Mathlib

theorem solution (tE tD dE dD : ℕ)
    (writes : 128 * 128 * 12582912 * 98304 + 256 * 12582912 * 98304 +
      12582912 * 98304 + 128 * 98304 + 98304 ≤ tE)
    (descE : dE = 6 * 1024 * 3^8 * 47) (descD : dD = 6 * 1024 * 3^8 * 47) :
    20584098424442880 ≤ tE + tD + (dE + dD) ∧
    4096 * (2 * 128 + 1) * 12582912^2 * 98304 = (16384250512316234068918272 : ℕ) := by
  subst dE
  subst dD
  norm_num at writes ⊢
  omega
