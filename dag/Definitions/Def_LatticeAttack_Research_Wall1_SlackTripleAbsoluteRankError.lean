import Definitions.Def_LatticeAttack_Research_Wall1_TripleAbsoluteRankError
import Definitions.Def_LatticeAttack_Research_Wall1_SlackThirdThreshold

set_option autoImplicit true

/-! A numerical absolute error mass for ordered candidate triples. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open Finset RawPrefixOccupancy CenteredPrefixOccupancy
open scoped Classical
local instance : Fact (Nat.Prime 3329) := ⟨by norm_num⟩

/-- The sum is over candidate triples, before grouping by their input blocks. -/
def slackTripleAbsoluteRankError : ℝ :=
  ∑ e ∈ distinctInputTriples (centeredBall 119 slackRadius),
    |AffineGraphMoments.rankWeight (fun i ↦ rawAffinePoint (e i).val) -
      1 / (3329 : ℝ)^1200|

theorem slackTripleAbsoluteRankError_le_masses :
    slackTripleAbsoluteRankError ≤ slackRankTwoTerm + slackCompatibleTripleTerm := by
  have h := AffineGraphMoments.sum_rankWeight_triple_abs_error
    (distinctInputTriples (centeredBall 119 slackRadius))
    (fun e i ↦ rawAffinePoint (e i).val)
    (raw_triple_inputs_ne _ (fun z hz ↦ ((mem_centeredBall slackRadius z).mp hz).2.1))
  have he : AffineGraphMoments.compatibleRankTwoTriples
      (distinctInputTriples (centeredBall 119 slackRadius))
      (fun e i ↦ rawAffinePoint (e i).val) =
      compatibleRankTwoTriples (centeredBall 119 slackRadius) := by
    unfold AffineGraphMoments.compatibleRankTwoTriples compatibleRankTwoTriples rankTwoTriples
    rw [filter_filter]
  rw [he] at h
  exact h

theorem slackTripleAbsoluteRankError_le_numeric :
    slackTripleAbsoluteRankError ≤ (2 : ℝ)/10^30 := by
  have hc : slackCompatibleTripleTerm ≤ (1 : ℝ)/10^30 :=
    (slackCompatibleTripleTerm_le_chernoff _ SlackTripleSectionNumeric.beta_pos.le).trans
      slackTripleChernoffBound_le_numeric
  have hr := slackRankTwoTerm_le_numeric
  have he : (5 : ℝ)/10^292 ≤ (1 : ℝ)/10^30 := by
    set_option exponentiation.threshold 1024 in norm_num
  have h := slackTripleAbsoluteRankError_le_masses
  linarith

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.slackTripleAbsoluteRankError_le_numeric
