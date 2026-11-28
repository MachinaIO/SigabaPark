import Definitions.Def_LatticeAttack_Research_Wall1_RawPrefixMean
import Definitions.Def_LatticeAttack_Research_Wall1_RawCenteredBallEquiv
import Definitions.Def_LatticeAttack_Research_Wall1_SharpCenteredLower

set_option autoImplicit true

/-! A geometric lower bound on the actual raw candidate mean. -/
noncomputable section
namespace SigabaNeo.Wall1.RawPrefixOccupancy
open RawBallRounding CenteredPrefixOccupancy

/-- Any radius in the exact slack-ball integer window yields this actual-mean bound. -/
theorem slackMean_ge_volume {R a : ℝ} (hR : 1690 ≤ R) (ha : 0 ≤ a)
    (ha2 : a^2 = R^2 - 517/4)
    (hlo : (8415829 : ℝ) ≤ R^2) (hhi : R^2 < 8415830) :
    (unitVolume 519 * a^519 -
      (Real.pi / Real.sqrt 2) * (unitVolume 518 * a^518) -
      2076 * Real.sqrt (R^2 - 1664^2 + 519/4)^519 * unitVolume 519) /
      (3329 : ℝ)^400 ≤ slackMean := by
  have h := centeredLifts_two_coordinate_lower (n := 517) hR ha (by simpa using ha2)
  have hc : (centeredLifts 519 R).card = (centeredBall 119 slackRadius).card := by
    rw [← slackBall_eq R hlo hhi]
    exact (slackBall_card_append (by linarith : 0 ≤ R)).symm
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at h
  rw [hc] at h
  unfold slackMean
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  convert h using 1 <;> norm_num

/-- The explicit geometric expression at the rational radius retaining the slack ball. -/
def slackVolumeLower : ℝ :=
    (unitVolume 519 * (Real.sqrt (841570066/100))^519 -
      (Real.pi / Real.sqrt 2) * (unitVolume 518 * (Real.sqrt (841570066/100))^518) -
      2076 * Real.sqrt (841582991/100 - 1664^2 + 519/4)^519 * unitVolume 519) /
      (3329 : ℝ)^400

/-- Only the numerical comparison of this explicit expression remains for the mean threshold. -/
theorem slackVolumeLower_le_mean : slackVolumeLower ≤ slackMean := by
  have hr : (Real.sqrt (841582991/100))^2 = (841582991/100 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have ha : (Real.sqrt (841570066/100))^2 = (841570066/100 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have h := slackMean_ge_volume
    (R := Real.sqrt (841582991/100)) (a := Real.sqrt (841570066/100))
    (by nlinarith [Real.sqrt_nonneg (841582991/100)]) (Real.sqrt_nonneg _)
    (by rw [ha, hr]; norm_num) (by rw [hr]; norm_num) (by rw [hr]; norm_num)
  simpa only [slackVolumeLower, hr] using h

end SigabaNeo.Wall1.RawPrefixOccupancy
#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slackMean_ge_volume

#print axioms SigabaNeo.Wall1.RawPrefixOccupancy.slackVolumeLower_le_mean
