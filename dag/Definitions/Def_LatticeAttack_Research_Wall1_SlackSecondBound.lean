import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondExact
import Definitions.Def_LatticeAttack_Research_Wall1_FiberSquareBound
import Definitions.Def_LatticeAttack_Research_Wall1_RawInputFiberBound

set_option autoImplicit true

/-! Geometric second-correction bound for the actual fixed candidate family. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy CenteredPrefixOccupancy CandidateInputPairs RawBallRounding

def slackFiberUpper : ℝ :=
  2 * Real.sqrt (slackRadius^2 + 400/4)^400 * unitVolume 400 / (3329 : ℝ)^400

def slackMeanUpper : ℝ :=
  2 * Real.sqrt (slackRadius^2 + 519/4)^519 * unitVolume 519 / (3329 : ℝ)^400

theorem slackFiberUpper_nonneg : 0 ≤ slackFiberUpper := by
  unfold slackFiberUpper unitVolume
  positivity

theorem slackMean_le_upper : slackMean ≤ slackMeanUpper := by
  have h := centeredBall_total_upper 119 slackRadius
  unfold slackMean slackMeanUpper
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using h

/-- The fiber-square term is controlled by the maximal normalized fiber and true mean. -/
theorem actualCorrection_two_le_fiber :
    |actualCorrection 2| ≤ slackFiberUpper * slackMean / 2 := by
  have hS := inputSquareSum_le_max_mul_card (centeredBall 119 slackRadius) Prod.snd
    (2 * Real.sqrt (slackRadius^2 + 400/4)^400 * unitVolume 400)
    (fun s _ ↦ centeredBall_inputFiber_upper 119 slackRadius s)
  rw [actualCorrection_two_abs]
  apply (div_le_div_of_nonneg_right hS (by positivity : (0:ℝ) ≤ 2 * 3329^800)).trans
  unfold slackFiberUpper slackMean
  have hp : (3329 : ℝ)^800 = ((3329 : ℝ)^400)^2 := by rw [← pow_mul]
  rw [hp]
  field_simp
  ring_nf <;> exact le_rfl

/-- A fully geometric upper expression with no moment-bound hypotheses. -/
theorem actualCorrection_two_le_geometric :
    |actualCorrection 2| ≤ slackFiberUpper * slackMeanUpper / 2 := by
  apply actualCorrection_two_le_fiber.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left slackMean_le_upper slackFiberUpper_nonneg) (by norm_num)

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualCorrection_two_le_geometric
