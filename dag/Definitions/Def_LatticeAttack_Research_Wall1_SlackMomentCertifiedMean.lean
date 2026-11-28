import Definitions.Def_LatticeAttack_Research_Wall1_SlackMomentCertificate
import Definitions.Def_LatticeAttack_Research_Wall1_SlackMeanThreshold

set_option autoImplicit true

/-! The high-radius moment certificate with its actual-mean premise discharged. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open RawPrefixOccupancy

/-- Only higher-correction bounds remain; the actual mean is proved geometrically. -/
theorem exit_probability_lt_reference_add_certified_mean (E : ℕ → ℝ)
    (herr : ∀ k, 2 ≤ k → k ≤ 24 → |actualCorrection k| ≤ E k) :
    exitProbability < (84896 / 100000000000000000 : ℝ) + correctionCharge E :=
  exit_probability_lt_reference_add slackMean_ge_threshold E herr

/-- Numerical high-radius target, conditional only on the higher corrections and charge.
This does not bound the low-radius complement or later BKZ tours. -/
theorem exit_probability_lt_target_certified_mean (E : ℕ → ℝ)
    (herr : ∀ k, 2 ≤ k → k ≤ 24 → |actualCorrection k| ≤ E k)
    (hcharge : correctionCharge E ≤ (225039 / 1000000000000000000 : ℝ)) :
    exitProbability < (1074 / 1000000000000000 : ℝ) :=
  exit_probability_lt_target slackMean_ge_threshold E herr hcharge

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_lt_reference_add_certified_mean
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.exit_probability_lt_target_certified_mean
