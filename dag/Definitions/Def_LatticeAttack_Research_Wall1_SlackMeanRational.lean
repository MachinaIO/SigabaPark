import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

set_option autoImplicit true

namespace SigabaNeo.Wall1.SlackMeanRational

def piLo : ℚ := 3.14159265358
def piHi : ℚ := 3.14159265360
def aLo : ℚ := 2900.9827059
def aHi : ℚ := 2900.9827060
def sqrtTwoLo : ℚ := 1.41421356237
def bHi : ℚ := 2376.356

def mainLower : ℚ :=
  ((piLo^259 * 2^260 / (Nat.doubleFactorial 519 : ℚ)) * aLo^519 -
    (piHi / sqrtTwoLo) * (piHi^259 / (Nat.factorial 259 : ℚ)) * aHi^518) / 3329^400

def capUpper : ℚ :=
  2076 * bHi^519 * (piHi^259 * 2^260 / (Nat.doubleFactorial 519 : ℚ)) / 3329^400

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem mainLower_bound : (58.51151 : ℚ) ≤ mainLower := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem capUpper_bound : capUpper ≤ (1 / 10^20 : ℚ) := by decide +kernel

theorem totalLower_bound : (58.5115 : ℚ) ≤ mainLower - capUpper := by
  have hm := mainLower_bound
  have hc := capUpper_bound
  norm_num at hc
  linarith

theorem explicitLower_bound : (58.5115 : ℚ) ≤
    ((piLo^259 * 2^260 / (Nat.doubleFactorial 519 : ℚ)) * aLo^519 -
      (piHi / sqrtTwoLo) * (piHi^259 / (Nat.factorial 259 : ℚ)) * aHi^518 -
      2076 * bHi^519 * (piHi^259 * 2^260 / (Nat.doubleFactorial 519 : ℚ))) / 3329^400 := by
  simpa only [mainLower, capUpper, ← sub_div] using totalLower_bound

theorem radius_rational_brackets :
    aLo^2 ≤ (8415700.66 : ℚ) ∧ (8415700.66 : ℚ) ≤ aHi^2 ∧
    sqrtTwoLo^2 ≤ 2 ∧ (8415829.91 - 1664^2 + 519/4 : ℚ) ≤ bHi^2 := by
  decide +kernel

end SigabaNeo.Wall1.SlackMeanRational
#print axioms SigabaNeo.Wall1.SlackMeanRational.mainLower_bound
#print axioms SigabaNeo.Wall1.SlackMeanRational.capUpper_bound
#print axioms SigabaNeo.Wall1.SlackMeanRational.totalLower_bound

#print axioms SigabaNeo.Wall1.SlackMeanRational.explicitLower_bound
#print axioms SigabaNeo.Wall1.SlackMeanRational.radius_rational_brackets
