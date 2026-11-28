import Definitions.Def_LatticeAttack_Research_Wall1_RawBallCount
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit true

/-! Exact unit-ball constants at the two dimensions used in the slack certificate. -/
noncomputable section
namespace SigabaNeo.Wall1.RawBallRounding
open MeasureTheory Metric

/-- Exact even-dimensional unit-ball volume; factorials remain symbolic. -/
theorem unitVolume_518 :
    unitVolume 518 = Real.pi^259 / (Nat.factorial 259 : ℝ) := by
  unfold unitVolume Measure.real
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 259) (by simp)]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (by positivity)

/-- Exact odd-dimensional unit-ball volume; the double factorial remains symbolic. -/
theorem unitVolume_519 :
    unitVolume 519 = Real.pi^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ) := by
  unfold unitVolume Measure.real
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 259) (by simp)]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, finrank_euclideanSpace_fin]
  exact ENNReal.toReal_ofReal (by positivity)

theorem unitVolume_518_pos : 0 < unitVolume 518 := by
  rw [unitVolume_518]
  exact div_pos (pow_pos Real.pi_pos _) (Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem unitVolume_519_pos : 0 < unitVolume 519 := by
  rw [unitVolume_519]
  exact div_pos (mul_pos (pow_pos Real.pi_pos _) (by positivity))
    (Nat.cast_pos.mpr (Nat.doubleFactorial_pos _))

end SigabaNeo.Wall1.RawBallRounding
#print axioms SigabaNeo.Wall1.RawBallRounding.unitVolume_518
#print axioms SigabaNeo.Wall1.RawBallRounding.unitVolume_519
#print axioms SigabaNeo.Wall1.RawBallRounding.unitVolume_518_pos
#print axioms SigabaNeo.Wall1.RawBallRounding.unitVolume_519_pos
