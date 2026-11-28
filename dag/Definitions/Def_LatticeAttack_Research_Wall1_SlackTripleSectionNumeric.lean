import Definitions.Def_LatticeAttack_Research_Wall1_ThetaElementaryBounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit true

/-! A rationally certified coarse bound for all short-normal theta sections. -/
noncomputable section
namespace SigabaNeo.Wall1.SlackTripleSectionNumeric

def beta : ℝ := 173 / 8415829

theorem beta_pos : 0 < beta := by norm_num [beta]

/-- Uniform section bound for every squared normal length in the certified interval. -/
theorem theta_product_le_84000 (D : ℝ) (hlo : 6 ≤ D) (hhi : D ≤ 6422) :
    thetaFactor (3*beta) * thetaFactor (beta*D/3) *
      thetaFactor (beta*(3329 : ℝ)^2/D) ≤ 84000 := by
  have hD : 0 < D := by linarith
  have hp : Real.pi ≤ (22 : ℝ)/7 := by linarith [Real.pi_lt_d20]
  let A := Real.sqrt (Real.pi/(3*beta))
  let B := Real.sqrt (Real.pi/(beta*D/3))
  let C := Real.sqrt (Real.pi/(beta*(3329 : ℝ)^2/D))
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hb := beta_pos
  have hA : A ≤ 227 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < 3*beta)).mpr
    norm_num [beta]
    linarith
  have hB : B ≤ 277 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < beta*D/3)).mpr
    norm_num [beta]
    nlinarith
  have hC : C ≤ 10 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < beta*(3329 : ℝ)^2/D)).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hD).mpr
    have hmul := mul_le_mul_of_nonneg_right hp hD.le
    norm_num [beta] at *
    nlinarith
  have hBC : B*C ≤ 80 := by
    change Real.sqrt _ * Real.sqrt _ ≤ _
    rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi/(beta*D/3))]
    have he : (Real.pi/(beta*D/3))*(Real.pi/(beta*(3329 : ℝ)^2/D)) =
        3*Real.pi^2/(beta^2*(3329 : ℝ)^2) := by
      field_simp
    rw [he]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ (by positivity : 0 < beta^2*(3329 : ℝ)^2)).mpr
    have hpi2 : Real.pi^2 ≤ ((22 : ℝ)/7)^2 :=
      pow_le_pow_left₀ Real.pi_pos.le hp 2
    norm_num [beta] at *
    nlinarith
  have htheta0 (a : ℝ) : 0 ≤ thetaFactor a := by
    unfold thetaFactor
    exact tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have htA : thetaFactor (3*beta) ≤ 228 :=
    (thetaFactor_le_one_add_sqrt (by positivity)).trans (by dsimp [A] at hA; linarith)
  have htB : thetaFactor (beta*D/3) ≤ 1+B :=
    thetaFactor_le_one_add_sqrt (by positivity)
  have htC : thetaFactor (beta*(3329 : ℝ)^2/D) ≤ 1+C :=
    thetaFactor_le_one_add_sqrt (by positivity)
  have hBCprod : thetaFactor (beta*D/3)*thetaFactor (beta*(3329 : ℝ)^2/D) ≤
      (1+B)*(1+C) := mul_le_mul htB htC (htheta0 _) (by positivity)
  have hmain := mul_le_mul htA hBCprod
    (mul_nonneg (htheta0 _) (htheta0 _)) (by norm_num : (0 : ℝ) ≤ 228)
  have hlast : 228*((1+B)*(1+C)) ≤ 84000 := by nlinarith
  apply le_trans ?_ hlast
  simpa only [mul_assoc] using hmain

end SigabaNeo.Wall1.SlackTripleSectionNumeric
#print axioms SigabaNeo.Wall1.SlackTripleSectionNumeric.theta_product_le_84000
