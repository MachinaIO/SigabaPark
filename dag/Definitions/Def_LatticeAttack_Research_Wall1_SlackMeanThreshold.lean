import Definitions.Def_LatticeAttack_Research_Wall1_SlackMeanRationalBound
import Definitions.Def_LatticeAttack_Research_Wall1_SlackMeanRational

set_option autoImplicit true

/-! Kernel-checked numerical lower bound for the actual slack-ball mean. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem slackRationalLower_ge_threshold : (58.5115 : ℝ) ≤ slackRationalLower := by
  have h : (58.5115 : ℝ) ≤
      ((SlackMeanRational.mainLower - SlackMeanRational.capUpper : ℚ) : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr SlackMeanRational.totalLower_bound
    simpa only [Rat.cast_ofScientific] using hh
  convert h using 1
  unfold slackRationalLower SlackMeanRational.mainLower SlackMeanRational.capUpper
    SlackMeanRational.piLo SlackMeanRational.piHi SlackMeanRational.aLo
    SlackMeanRational.aHi SlackMeanRational.sqrtTwoLo SlackMeanRational.bHi
  push_cast
  ring

/-- The actual fixed candidate family has mean at least58.5115. -/
theorem slackMean_ge_threshold : (58.5115 : ℝ) ≤ slackMean :=
  slackRationalLower_ge_threshold.trans
    (slackRationalLower_le_volume.trans slackVolumeLower_le_mean)

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slackRationalLower_ge_threshold
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slackMean_ge_threshold
