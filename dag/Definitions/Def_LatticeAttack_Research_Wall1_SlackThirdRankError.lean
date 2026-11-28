import Definitions.Def_LatticeAttack_Research_Wall1_RawRankTwoCount
import Definitions.Def_LatticeAttack_Research_Wall1_CenteredInputReduction
import Definitions.Def_LatticeAttack_Research_Wall1_SlackThirdRepeatedBound

set_option autoImplicit true

/-! The third factorial cumulant differs negligibly from its compatible rank-two mass. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy CenteredPrefixOccupancy RawBallRounding

/-- Normalized count of all rank-two triples, including inconsistent ones. -/
def slackRankTwoTerm : ℝ :=
  (rankTwoTriples (centeredBall 119 slackRadius)).card / (3329 : ℝ)^1200

/-- The compatible rank-two incidence contribution, which still needs geometry. -/
def slackCompatibleTripleTerm : ℝ :=
  (compatibleRankTwoTriples (centeredBall 119 slackRadius)).card / (3329 : ℝ)^800

theorem slackRankTwoTerm_nonneg : 0 ≤ slackRankTwoTerm := by
  unfold slackRankTwoTerm
  positivity

theorem slackRankTwoTerm_le_fiber :
    slackRankTwoTerm ≤ 3329 * slackMean^2 * slackFiberUpper := by
  have h := rankTwoTriples_card_le (centeredBall 119 slackRadius)
    (fun z hz ↦ ((mem_centeredBall slackRadius z).mp hz).2.1)
    (2 * Real.sqrt (slackRadius^2 + 400/4)^400 * unitVolume 400)
    (centeredBall_reduced_inputFiber_upper 119 slackRadius)
  unfold slackRankTwoTerm slackMean slackFiberUpper
  apply (div_le_div_of_nonneg_right h (by positivity : (0:ℝ) ≤ 3329^1200)).trans_eq
  have hp : (3329 : ℝ)^1200 = ((3329 : ℝ)^400)^3 := by rw [← pow_mul]
  rw [hp]
  ring

theorem slackRankTwoTerm_le_numeric : slackRankTwoTerm ≤ (5 : ℝ)/10^292 := by
  have hmu : slackMean ≤ 119 := slackMean_le_upper.trans slackMeanUpper_le_119
  have hmu0 : 0 ≤ slackMean := by unfold slackMean; positivity
  have hmu2 : slackMean^2 ≤ (119 : ℝ)^2 := pow_le_pow_left₀ hmu0 hmu 2
  apply slackRankTwoTerm_le_fiber.trans
  calc
    _ ≤ 3329 * (119 : ℝ)^2 * ((9 : ℝ)/10^300) := by
      gcongr
      · exact slackFiberUpper_nonneg
      · exact slackFiberUpper_le_numeric
    _ ≤ _ := by
      set_option exponentiation.threshold 2048 in norm_num

/-- A certified third-order cumulant error, leaving only the compatible mass. -/
theorem actualFactorialCumulant_three_error :
    |actualFactorialCumulant 3 - slackCompatibleTripleTerm| ≤ (5 : ℝ)/10^292 := by
  have hcube : slackCubeTerm ≤ (5 : ℝ)/10^292 := slackCubeTerm_le_numeric.trans (by
    set_option exponentiation.threshold 2048 in norm_num)
  have hA := slackRankTwoTerm_le_numeric
  have hA0 := slackRankTwoTerm_nonneg
  have hC0 := slackCubeTerm_nonneg
  have he : actualFactorialCumulant 3 - slackCompatibleTripleTerm =
      slackCubeTerm - slackRankTwoTerm := by
    rw [actualFactorialCumulant_three_decomposition]
    unfold slackCompatibleTripleTerm slackRankTwoTerm
    ring
  rw [he, abs_le]
  constructor <;> linarith

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.slackRankTwoTerm_le_numeric
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualFactorialCumulant_three_error
