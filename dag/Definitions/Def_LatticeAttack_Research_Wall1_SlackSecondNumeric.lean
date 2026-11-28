import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic
set_option autoImplicit true

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace SigabaNeo.Wall1.SlackSecondNumeric

def piHi : ℚ := 3.14160

def b : ℚ := 2901.03

def muUpper : ℚ :=
  2 * (piHi ^ 259 * 2 ^ 260 / (519 : ℕ).doubleFactorial) * b ^ 519 / 3329 ^ 400

def rhoUpper : ℚ :=
  2 * (piHi ^ 200 / (200 : ℕ).factorial) * (8415929 : ℚ) ^ 200 / 3329 ^ 400

theorem b_squared : (8415829 : ℚ) + 519 / 4 ≤ b ^ 2 := by decide +kernel

theorem muUpper_le : muUpper ≤ 119 := by decide +kernel

theorem rhoUpper_le : rhoUpper ≤ (9 : ℚ) / 10 ^ 300 := by decide +kernel

#print axioms b_squared
#print axioms muUpper_le
#print axioms rhoUpper_le
end SigabaNeo.Wall1.SlackSecondNumeric
