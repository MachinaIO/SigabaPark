import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondUpperRational
import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondNumeric

set_option autoImplicit true

/-! Kernel-certified numerical bound for the actual second canonical correction. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy

private theorem mean_rational_cast :
    (SlackSecondNumeric.muUpper : ℝ) = secondMeanRationalUpper := by
  unfold SlackSecondNumeric.muUpper SlackSecondNumeric.piHi SlackSecondNumeric.b
    secondMeanRationalUpper
  push_cast
  rfl

private theorem fiber_rational_cast :
    (SlackSecondNumeric.rhoUpper : ℝ) = secondFiberRationalUpper := by
  unfold SlackSecondNumeric.rhoUpper SlackSecondNumeric.piHi secondFiberRationalUpper
  push_cast
  rfl

theorem slackMeanUpper_le_119 : slackMeanUpper ≤ 119 := by
  have h := (Rat.cast_le (K := ℝ)).mpr SlackSecondNumeric.muUpper_le
  rw [mean_rational_cast] at h
  exact slackMeanUpper_le_rational.trans (by exact_mod_cast h)

theorem slackFiberUpper_le_numeric : slackFiberUpper ≤ (9 : ℝ)/10^300 := by
  have h := (Rat.cast_le (K := ℝ)).mpr SlackSecondNumeric.rhoUpper_le
  rw [fiber_rational_cast] at h
  push_cast at h
  exact slackFiberUpper_le_rational.trans h

/-- The actual second correction fits a conservative10^-297 absolute budget. -/
theorem actualCorrection_two_le_numeric : |actualCorrection 2| ≤ (1 : ℝ)/10^297 := by
  apply actualCorrection_two_le_geometric.trans
  have h : slackFiberUpper * slackMeanUpper ≤ ((9 : ℝ)/10^300) * 119 := by
    exact mul_le_mul slackFiberUpper_le_numeric slackMeanUpper_le_119
      (by unfold slackMeanUpper RawBallRounding.unitVolume; positivity) (by positivity)
  apply (div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 2)).trans
  set_option exponentiation.threshold 1024 in norm_num

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_two_le_numeric
