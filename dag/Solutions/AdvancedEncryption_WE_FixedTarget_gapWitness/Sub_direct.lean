import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution (rho a : ℝ) (n : ℕ) (ha : 0 ≤ a)
    (h : a ≤ rho^(3*n)) : a^5 ≤ (rho^(5*n))^3 := by
  calc
    a^5 ≤ (rho^(3*n))^5 := pow_le_pow_left₀ ha h 5
    _ = (rho^(5*n))^3 := by rw [←pow_mul, ←pow_mul]; congr 1; omega
