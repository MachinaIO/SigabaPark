import Definitions.Def_LatticeAttack_Research_Wall1_SlackMomentCertifiedMean
import Definitions.Def_LatticeAttack_Research_Wall1_SlackSecondThreshold

set_option autoImplicit true

/-! High-radius target with the actual mean and second correction discharged. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate

/-- Insert the proved second-order budget into a higher-order envelope. -/
def withCertifiedSecond (E : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 2 then 1 / 10^297 else E k

/-- Only orders3..24 and their weighted numerical charge remain as premises. -/
theorem exit_probability_lt_target_from_third_order (E : ℕ → ℝ)
    (herr : ∀ k, 3 ≤ k → k ≤ 24 → |actualCorrection k| ≤ E k)
    (hcharge : correctionCharge (withCertifiedSecond E) ≤
      (225039 / 1000000000000000000 : ℝ)) :
    exitProbability < (1074 / 1000000000000000 : ℝ) := by
  apply exit_probability_lt_target_certified_mean (withCertifiedSecond E) ?_ hcharge
  intro k hk hmax
  by_cases h : k = 2
  · subst k
    simpa only [withCertifiedSecond, ite_true] using actualCorrection_two_le_numeric
  · simpa only [withCertifiedSecond, h, ite_false] using herr k (by omega) hmax

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_lt_target_from_third_order
