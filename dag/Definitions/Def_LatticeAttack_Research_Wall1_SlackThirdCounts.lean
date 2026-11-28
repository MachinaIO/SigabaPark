import Definitions.Def_LatticeAttack_Research_Wall1_RawThirdMomentExact
import Definitions.Def_LatticeAttack_Research_Wall1_SlackThirdIdentity

set_option autoImplicit true

/-! The third actual factorial cumulant is an exact exceptional-triple count. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy CenteredPrefixOccupancy CandidateInputPairs FactorialMomentTransfer

/-- The independent rank-three contribution cancels from the third cumulant.
The remaining exceptional counts still require quantitative bounds. -/
theorem actualFactorialCumulant_three_counts :
    actualFactorialCumulant 3 =
      (2 * (inputCubeSum (centeredBall 119 slackRadius) Prod.snd : ℝ) -
        (rankTwoTriples (centeredBall 119 slackRadius)).card) / (3329 : ℝ)^1200 +
        (compatibleRankTwoTriples (centeredBall 119 slackRadius)).card / (3329 : ℝ)^800 := by
  have hF := raw_third_factorial_exact (by decide : 119 ≤ 512)
    (centeredBall 119 slackRadius)
    (fun z hz ↦ ((mem_centeredBall slackRadius z).mp hz).1)
    (fun z hz ↦ ((mem_centeredBall slackRadius z).mp hz).2.1)
  change factorialAverage slackCount 3 = _ at hF
  rw [actualFactorialCumulant_three_from_second, hF, actualCorrection_two_exact]
  unfold slackMean slackInputSquareSum
  have h800 : (3329 : ℝ)^800 = ((3329 : ℝ)^400)^2 := by rw [← pow_mul]
  have h1200 : (3329 : ℝ)^1200 = ((3329 : ℝ)^400)^3 := by rw [← pow_mul]
  rw [h800, h1200]
  have hQ : (3329 : ℝ)^400 ≠ 0 := pow_ne_zero _ (by norm_num)
  generalize (3329 : ℝ)^400 = Q at *
  field_simp
  <;> ring

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualFactorialCumulant_three_counts
