import Definitions.Def_LatticeAttack_Research_Wall1_RawSlackMeanLower
import Definitions.Def_LatticeAttack_Research_Wall1_SlackVolumeConstants
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit true

/-! Directed rational bounds for the concrete slack-ball volume expression. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open RawBallRounding

/-- A rational lower approximation, with signs directed before evaluation. -/
def slackRationalLower : ℝ :=
  (((3.14159265358 : ℝ)^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ)) * 2900.9827059^519 -
    (3.14159265360 / 1.41421356237) *
      (3.14159265360^259 / (Nat.factorial 259 : ℝ)) * 2900.9827060^518 -
    2076 * 2376.356^519 *
      (3.14159265360^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ))) / 3329^400

theorem slackRationalLower_le_volume : slackRationalLower ≤ slackVolumeLower := by
  have hpl : (3.14159265358 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d20]
  have hpu : Real.pi ≤ (3.14159265360 : ℝ) := by linarith [Real.pi_lt_d20]
  have hal : (2900.9827059 : ℝ) ≤ Real.sqrt (841570066/100) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 841570066/100),
      Real.sqrt_nonneg (841570066/100)]
  have hau : Real.sqrt (841570066/100) ≤ (2900.9827060 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 841570066/100),
      Real.sqrt_nonneg (841570066/100)]
  have hsl : (1.41421356237 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  have hbu : Real.sqrt (841582991/100 - 1664^2 + 519/4) ≤ (2376.356 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 841582991/100 - 1664^2 + 519/4),
      Real.sqrt_nonneg (841582991/100 - 1664^2 + 519/4 : ℝ)]
  have hfirst :
      ((3.14159265358 : ℝ)^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ)) * 2900.9827059^519 ≤
      (Real.pi^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ)) *
        (Real.sqrt (841570066/100))^519 := by
    gcongr
  have hsecond : (Real.pi / Real.sqrt 2) *
      (Real.pi^259 / (Nat.factorial 259 : ℝ) * (Real.sqrt (841570066/100))^518) ≤
      (3.14159265360 / 1.41421356237) *
        (3.14159265360^259 / (Nat.factorial 259 : ℝ)) * 2900.9827060^518 := by
    rw [← mul_assoc]
    gcongr
  have hthird : 2076 * Real.sqrt (841582991/100 - 1664^2 + 519/4)^519 *
      (Real.pi^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ)) ≤
      2076 * 2376.356^519 *
        (3.14159265360^259 * 2^260 / (Nat.doubleFactorial 519 : ℝ)) := by
    gcongr
  unfold slackRationalLower slackVolumeLower
  rw [unitVolume_518, unitVolume_519]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  linarith

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slackRationalLower_le_volume
