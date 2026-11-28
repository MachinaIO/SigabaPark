import Definitions.Def_LatticeAttack_Research_Wall1_RawCompatibleChernoff
import Definitions.Def_LatticeAttack_Research_Wall1_SlackThirdRankError

set_option autoImplicit true

/-! The actual third cumulant is bounded by scalar Gaussian sections and a certified error. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open Finset RawPrefixOccupancy CenteredPrefixOccupancy AffineTripleChernoff
open scoped Classical

/-- The only remaining third-order analytic quantity is the finite scalar partition sum. -/
def slackTripleChernoffBound (β : ℝ) : ℝ :=
  Real.exp (3 * β * slackRadius^2) *
    (∑ t ∈ (univ : Finset (ZMod 3329)).filter (fun t ↦ t ≠ 0 ∧ t ≠ 1),
      (scalarPartition t β)^519) / (3329 : ℝ)^800

theorem slackCompatibleTripleTerm_le_chernoff (β : ℝ) (hβ : 0 ≤ β) :
    slackCompatibleTripleTerm ≤ slackTripleChernoffBound β := by
  have h := raw_compatible_card_le_scalarPartitions 119 slackRadius β hβ
  unfold slackCompatibleTripleTerm slackTripleChernoffBound
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact h

/-- A bound for the actual third factorial cumulant, with all counting bridges
and repeated-input errors discharged. Numerical scalar-section estimates remain. -/
theorem actualFactorialCumulant_three_le_chernoff (β : ℝ) (hβ : 0 ≤ β) :
    |actualFactorialCumulant 3| ≤ slackTripleChernoffBound β + (5 : ℝ)/10^292 := by
  have he := abs_le.mp actualFactorialCumulant_three_error
  have hu := slackCompatibleTripleTerm_le_chernoff β hβ
  have hB : 0 ≤ slackCompatibleTripleTerm := by
    unfold slackCompatibleTripleTerm
    positivity
  rw [abs_le]
  constructor <;> linarith

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualFactorialCumulant_three_le_chernoff
