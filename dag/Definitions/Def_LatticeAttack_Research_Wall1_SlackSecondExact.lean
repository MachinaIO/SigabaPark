import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondCorrection
import Definitions.Def_LatticeAttack_Research_Wall1_RawSecondMomentExact

set_option autoImplicit true

/-! The actual second slack correction is an explicit nonpositive fiber-square term. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy CenteredPrefixOccupancy CandidateInputPairs FactorialMomentTransfer

/-- Input-fiber squares count all same-input pairs, including the diagonal. -/
def slackInputSquareSum : ℕ := inputSquareSum (centeredBall 119 slackRadius) Prod.snd

/-- Exact sign and magnitude of the second canonical correction for the actual family. -/
theorem actualCorrection_two_exact :
    actualCorrection 2 = -(slackInputSquareSum : ℝ) / (2 * (3329 : ℝ)^800) := by
  have hF := raw_second_factorial_exact (by decide : 119 ≤ 512)
    (centeredBall 119 slackRadius)
    (fun z hz ↦ ((mem_centeredBall slackRadius z).mp hz).1)
    (fun z hz ↦ ((mem_centeredBall slackRadius z).mp hz).2.1)
  rw [actualCorrection_two]
  change factorialAverage _ _ = _ at hF
  change (factorialAverage (rawCount (by decide : 119 ≤ 512)
    (centeredBall 119 slackRadius)) 2 - slackMean^2) / 2 = _
  rw [hF]
  unfold slackMean slackInputSquareSum
  rw [div_pow, ← pow_mul]
  norm_num only [Nat.reduceMul]
  ring

theorem actualCorrection_two_nonpos : actualCorrection 2 ≤ 0 := by
  rw [actualCorrection_two_exact]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem actualCorrection_two_abs :
    |actualCorrection 2| = (slackInputSquareSum : ℝ) / (2 * (3329 : ℝ)^800) := by
  rw [abs_of_nonpos actualCorrection_two_nonpos, actualCorrection_two_exact]
  ring

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_two_exact
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_two_nonpos
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_two_abs
