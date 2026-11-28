import Definitions.Def_LatticeAttack_Research_Wall1_SlackThirdCounts
import Definitions.Def_LatticeAttack_Research_Wall1_FiberCubeBound
import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondThreshold

set_option autoImplicit true

/-! Numerical control of the repeated-input cube term in the third cumulant. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy CenteredPrefixOccupancy CandidateInputPairs RawBallRounding

/-- The cube term normalized by three powers of the label-space size. -/
def slackCubeTerm : ℝ :=
  2 * (inputCubeSum (centeredBall 119 slackRadius) Prod.snd : ℝ) / (3329 : ℝ)^1200

theorem slackCubeTerm_nonneg : 0 ≤ slackCubeTerm := by
  unfold slackCubeTerm
  positivity

theorem slackCubeTerm_le_fiber :
    slackCubeTerm ≤ 2 * slackFiberUpper^2 * slackMean := by
  have h := inputCubeSum_le_max_sq_mul_card (centeredBall 119 slackRadius) Prod.snd
    (2 * Real.sqrt (slackRadius^2 + 400/4)^400 * unitVolume 400)
    (by unfold unitVolume; positivity)
    (fun s _ ↦ centeredBall_inputFiber_upper 119 slackRadius s)
  unfold slackCubeTerm slackFiberUpper slackMean
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num))
    (by positivity : (0:ℝ) ≤ 3329^1200)).trans_eq
  have hp : (3329 : ℝ)^1200 = ((3329 : ℝ)^400)^3 := by rw [← pow_mul]
  rw [hp]
  ring

/-- An unconditional bound; it does not control the rank-two triple terms. -/
theorem slackCubeTerm_le_numeric : slackCubeTerm ≤ (2 : ℝ)/10^596 := by
  have hmu : slackMean ≤ 119 := slackMean_le_upper.trans slackMeanUpper_le_119
  have hρ : slackFiberUpper^2 ≤ ((9 : ℝ)/10^300)^2 := by
    exact pow_le_pow_left₀ slackFiberUpper_nonneg slackFiberUpper_le_numeric 2
  apply slackCubeTerm_le_fiber.trans
  calc
    _ ≤ 2 * (((9 : ℝ)/10^300)^2) * 119 := by
      gcongr
      unfold slackMean
      positivity
    _ ≤ _ := by
      set_option exponentiation.threshold 2048 in norm_num

/-- Separate the two exceptional triple terms from the now bounded cube term. -/
theorem actualFactorialCumulant_three_decomposition :
    actualFactorialCumulant 3 = slackCubeTerm -
      (rankTwoTriples (centeredBall 119 slackRadius)).card / (3329 : ℝ)^1200 +
      (compatibleRankTwoTriples (centeredBall 119 slackRadius)).card / (3329 : ℝ)^800 := by
  rw [actualFactorialCumulant_three_counts]
  unfold slackCubeTerm
  ring

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.slackCubeTerm_le_numeric
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualFactorialCumulant_three_decomposition
