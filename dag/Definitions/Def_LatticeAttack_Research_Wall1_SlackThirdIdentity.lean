import Definitions.Def_LatticeAttack_Research_Wall1_ThirdFactorialCumulant
import Definitions.Def_LatticeAttack_Research_Wall1_SlackCumulantMajorant

set_option autoImplicit true

/-! Exact third-order identities for the actual slack count; no third-order bound is asserted. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open FactorialMomentTransfer RawPrefixOccupancy ExponentialCoefficientRecurrence

theorem actualFactorialCumulant_three :
    actualFactorialCumulant 3 = factorialAverage slackCount 3 -
      3 * slackMean * factorialAverage slackCount 2 + 2 * slackMean^3 := by
  have h := factorialCumulant_three (factorialAverage slackCount) (factorialAverage_zero _)
  have hm : factorialAverage slackCount 1 = slackMean := slack_first_factorial_average
  simpa only [hm, actualFactorialCumulant] using h

/-- The already controlled second correction isolates the remaining third factorial moment. -/
theorem actualFactorialCumulant_three_from_second :
    actualFactorialCumulant 3 = factorialAverage slackCount 3 - slackMean^3 -
      6 * slackMean * actualCorrection 2 := by
  rw [actualFactorialCumulant_three, actualCorrection_two]
  ring

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualFactorialCumulant_three_from_second
