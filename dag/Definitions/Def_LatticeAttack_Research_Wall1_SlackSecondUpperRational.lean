import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondBound
import Definitions.Def_LatticeAttack_Research_Wall1_SlackVolumeConstants
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit true

/-! Rational upper expressions for the exact geometric second-moment bound. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy CenteredPrefixOccupancy RawBallRounding MeasureTheory Metric

/-- Rational upper expression for the total normalized candidate count. -/
def secondMeanRationalUpper : ℝ :=
  2 * (3.14160^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ)) *
    2901.03^519 / (3329 : ℝ)^400

/-- Rational upper expression for the maximal normalized input fiber. -/
def secondFiberRationalUpper : ℝ :=
  2 * (3.14160^200 / (Nat.factorial 200 : ℝ)) *
    8415929^200 / (3329 : ℝ)^400

theorem unitVolume_400 :
    unitVolume 400 = Real.pi^200 / (Nat.factorial 200 : ℝ) := by
  unfold unitVolume Measure.real
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 200) (by simp)]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  exact ENNReal.toReal_ofReal (by positivity)

private theorem slackRadius_sq : slackRadius^2 = 8415829 := by
  exact Real.sq_sqrt (by norm_num)

private theorem mean_sqrt_le :
    Real.sqrt (slackRadius^2 + 519/4) ≤ (2901.03 : ℝ) := by
  apply (Real.sqrt_le_left (by norm_num)).2
  rw [slackRadius_sq]
  norm_num

private theorem fiber_sqrt_pow :
    Real.sqrt (slackRadius^2 + 400/4)^400 = (8415929 : ℝ)^200 := by
  rw [show (400 : ℕ) = 2*200 from rfl, pow_mul,
    Real.sq_sqrt (by positivity), slackRadius_sq]
  norm_num only [show (8415829 : ℝ) + 400/4 = 8415929 by norm_num]

theorem slackMeanUpper_le_rational : slackMeanUpper ≤ secondMeanRationalUpper := by
  unfold slackMeanUpper secondMeanRationalUpper
  rw [unitVolume_519]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  calc
    _ ≤ 2 * (2901.03 : ℝ)^519 *
        (3.14160^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ)) := by
      gcongr
      · exact mean_sqrt_le
      · exact Real.pi_lt_d4.le.trans (by norm_num)
    _ = _ := by ring

theorem slackFiberUpper_le_rational : slackFiberUpper ≤ secondFiberRationalUpper := by
  unfold slackFiberUpper secondFiberRationalUpper
  rw [unitVolume_400, fiber_sqrt_pow]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  calc
    _ ≤ 2 * (8415929 : ℝ)^200 * (3.14160^200 / (Nat.factorial 200 : ℝ)) := by
      gcongr
      exact Real.pi_lt_d4.le.trans (by norm_num)
    _ = _ := by ring

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.slackMeanUpper_le_rational
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.slackFiberUpper_le_rational
