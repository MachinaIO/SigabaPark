import Definitions.Def_LatticeAttack_Research_Wall1_SlackMomentCertificate
import Definitions.Def_LatticeAttack_Research_Wall1_CanonicalSecondCorrection
import Definitions.Def_LatticeAttack_Research_Wall1_RawSecondMoment

set_option autoImplicit true

/-! Exact second correction for the actual slack count, before pair probability bounds. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy FactorialMomentTransfer ControlledPlane TerminalProjection
open CenteredPrefixOccupancy

/-- The second canonical correction is the actual second factorial discrepancy. -/
theorem actualCorrection_two :
    actualCorrection 2 = (factorialAverage slackCount 2 - slackMean^2) / 2 := by
  apply canonicalCorrection_two_normalized
  · exact factorialAverage_zero _
  · exact slack_first_factorial_average

/-- This is an exact average over original matrices, with no selected-history conditioning. -/
theorem actualCorrection_two_collisions :
    actualCorrection 2 =
      ((∑ A, ((collisionPairs (centeredBall 119 slackRadius)
        (rawSyndrome (by decide : 119 ≤ 512) A)).card : ℝ)) /
        ((Fintype.card Sample : ℝ) * Fintype.card Column) - slackMean^2) / 2 := by
  rw [actualCorrection_two]
  change (factorialAverage
    (rawCount (by decide : 119 ≤ 512) (centeredBall 119 slackRadius)) 2 - slackMean^2) / 2 = _
  rw [raw_second_factorial_average]

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_two
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_two_collisions
