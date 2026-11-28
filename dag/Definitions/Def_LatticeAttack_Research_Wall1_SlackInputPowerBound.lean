import Definitions.Def_LatticeAttack_Research_Wall1_FiberPowerBound
import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondThreshold

set_option autoImplicit true

/-! Numerical bounds for same-input power sums at every positive order. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy CenteredPrefixOccupancy CandidateInputPairs RawBallRounding

/-- All entries in this term share one input; mixed input partitions are not included. -/
theorem slack_inputPowerSum_le_fiber (n : ℕ) :
    (inputPowerSum (centeredBall 119 slackRadius) Prod.snd (n+1) : ℝ) /
      ((3329 : ℝ)^400)^(n+1) ≤ slackFiberUpper^n * slackMean := by
  have h := inputPowerSum_succ_le (centeredBall 119 slackRadius) Prod.snd
    (2 * Real.sqrt (slackRadius^2 + 400/4)^400 * unitVolume 400)
    (fun s _ ↦ centeredBall_inputFiber_upper 119 slackRadius s) n
  apply (div_le_div_of_nonneg_right h (by positivity : (0:ℝ) ≤ (3329^400)^(n+1))).trans_eq
  unfold slackFiberUpper slackMean
  rw [div_pow, pow_succ]
  ring

/-- Uniform certified bound for the fully repeated-input term at every order. -/
theorem slack_inputPowerSum_le_numeric (n : ℕ) :
    (inputPowerSum (centeredBall 119 slackRadius) Prod.snd (n+1) : ℝ) /
      ((3329 : ℝ)^400)^(n+1) ≤ 119 * ((9 : ℝ)/10^300)^n := by
  apply (slack_inputPowerSum_le_fiber n).trans
  have hm := slackMean_le_upper.trans slackMeanUpper_le_119
  have hp := pow_le_pow_left₀ slackFiberUpper_nonneg slackFiberUpper_le_numeric n
  have h := mul_le_mul hp hm (by unfold slackMean; positivity)
    (pow_nonneg (by positivity : (0:ℝ) ≤ 9/10^300) n)
  simpa only [mul_comm] using h

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.slack_inputPowerSum_le_numeric
