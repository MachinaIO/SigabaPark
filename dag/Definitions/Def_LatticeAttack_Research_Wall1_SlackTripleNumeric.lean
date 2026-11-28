import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit true

/-! Conservative exact arithmetic for the third-order Gaussian certificate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace SigabaNeo.Wall1.SlackTripleNumeric

def rationalUpper : ℚ := (68/25 : ℚ)^519 * 3327 * 84000^519 / 3329^800

theorem rationalUpper_le : rationalUpper ≤ (1 : ℚ)/10^30 := by decide +kernel

theorem exp_519_le : Real.exp 519 ≤ (68/25 : ℝ)^519 := by
  have h : Real.exp 1 ≤ (68/25 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le h 519
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hp

theorem realUpper_le : (68/25 : ℝ)^519 * 3327 * 84000^519 / 3329^800 ≤
    (1 : ℝ)/10^30 := by
  have h := (Rat.cast_le (K := ℝ)).mpr rationalUpper_le
  unfold rationalUpper at h
  push_cast at h
  exact h

end SigabaNeo.Wall1.SlackTripleNumeric
#print axioms SigabaNeo.Wall1.SlackTripleNumeric.rationalUpper_le
#print axioms SigabaNeo.Wall1.SlackTripleNumeric.realUpper_le
