import Definitions.Def_LatticeAttack_Research_Wall1_SlackThirdChernoff
import Definitions.Def_LatticeAttack_Research_Wall1_SlackTripleSectionNumeric
import Definitions.Def_LatticeAttack_Research_Wall1_SlackTripleNumeric
import Definitions.Def_LatticeAttack_Research_Wall1_AffineNormalTheta

set_option autoImplicit true

/-! Unconditional numerical bound for the actual third factorial cumulant. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackMomentCertificate
open Finset RawPrefixOccupancy CenteredPrefixOccupancy AffineTripleChernoff
open scoped Classical

lemma scalarPartition_nonneg (t : ZMod 3329) (β : ℝ) : 0 ≤ scalarPartition t β :=
  sum_nonneg fun _ _ ↦ (Real.exp_pos _).le

/-- A uniform scalar bound suffices; the finer norm histogram is not needed at order three. -/
theorem slack_scalarPartition_le (t : ZMod 3329) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    scalarPartition t SlackTripleSectionNumeric.beta ≤ 84000 := by
  obtain ⟨u,v,w,hs,hg,hlo,hhi,he⟩ := scalarPartition_eq_short_normal t ht0 ht1
    SlackTripleSectionNumeric.beta
  have hlo' : (6 : ℝ) ≤ (u:ℝ)^2 + (v:ℝ)^2 + (w:ℝ)^2 := by
    simp only [pow_two]
    exact_mod_cast hlo
  have hhi' : (u:ℝ)^2 + (v:ℝ)^2 + (w:ℝ)^2 ≤ (6422:ℝ) := by
    simp only [pow_two]
    exact_mod_cast hhi
  rw [he]
  exact (normalPartition_le_theta_product u v w _ hs hg
    (by unfold SlackTripleSectionNumeric.beta; positivity) (by linarith)).trans
    (SlackTripleSectionNumeric.theta_product_le_84000 _ hlo' hhi')

lemma nontrivial_parameter_card :
    ((univ : Finset (ZMod 3329)).filter (fun t ↦ t ≠ 0 ∧ t ≠ 1)).card = 3327 := by
  have he : ((univ : Finset (ZMod 3329)).filter (fun t ↦ t ≠ 0 ∧ t ≠ 1)) =
      univ \ {0,1} := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_insert, mem_singleton]
    tauto
  rw [he, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
  rw [card_pair (by decide : (0 : ZMod 3329) ≠ 1)]

theorem slackTripleChernoffBound_le_numeric :
    slackTripleChernoffBound SlackTripleSectionNumeric.beta ≤ (1:ℝ)/10^30 := by
  have hs : (∑ t ∈ (univ : Finset (ZMod 3329)).filter (fun t ↦ t ≠ 0 ∧ t ≠ 1),
      (scalarPartition t SlackTripleSectionNumeric.beta)^519) ≤
      3327 * (84000:ℝ)^519 := by
    calc
      _ ≤ ∑ _t ∈ (univ : Finset (ZMod 3329)).filter (fun t ↦ t ≠ 0 ∧ t ≠ 1),
          (84000:ℝ)^519 := by
        apply sum_le_sum
        intro t ht
        exact pow_le_pow_left₀ (scalarPartition_nonneg _ _)
          (slack_scalarPartition_le t (mem_filter.mp ht).2.1 (mem_filter.mp ht).2.2) 519
      _ = _ := by simp only [sum_const, nsmul_eq_mul, nontrivial_parameter_card, Nat.cast_ofNat]
  have hex : 3 * SlackTripleSectionNumeric.beta * slackRadius^2 = (519:ℝ) := by
    unfold SlackTripleSectionNumeric.beta slackRadius
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8415829)]
    norm_num
  unfold slackTripleChernoffBound
  rw [hex]
  have hm := mul_le_mul SlackTripleNumeric.exp_519_le hs
    (sum_nonneg fun t _ ↦ pow_nonneg (scalarPartition_nonneg _ _) _) (by positivity)
  apply (div_le_div_of_nonneg_right hm (by positivity : (0:ℝ) ≤ 3329^800)).trans
  simpa only [mul_assoc] using SlackTripleNumeric.realUpper_le

/-- Third order is quantitatively closed for the original fixed-family law. -/
theorem actualFactorialCumulant_three_le_numeric :
    |actualFactorialCumulant 3| ≤ (2:ℝ)/10^30 := by
  have h := actualFactorialCumulant_three_le_chernoff SlackTripleSectionNumeric.beta
    (by unfold SlackTripleSectionNumeric.beta; positivity)
  have hn := slackTripleChernoffBound_le_numeric
  have he : (5:ℝ)/10^292 ≤ (1:ℝ)/10^30 := by
    set_option exponentiation.threshold 1024 in norm_num
  linarith

end SigabaNeo.Wall1.SlackMomentCertificate
#print axioms SigabaNeo.Wall1.SlackMomentCertificate.actualFactorialCumulant_three_le_numeric
