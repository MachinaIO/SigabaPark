import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLensMoments506
import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLensDisk506

set_option autoImplicit true

/-! The Euclidean off-diagonal lens integral in dimension 506. -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506
open Real Metric MeasureTheory Set TerminalProjection
open scoped RealInnerProductSpace Classical
private abbrev F := EuclideanSpace ℝ (Fin 505)
private abbrev W := WindowSpace F

private def cut (a b d U y : ℝ) :=
  if (y/d)^2+a^2 < U ∧ (y/d)^2+b^2 < U then sphericalKernel (Radial.angle a b ((y/d)^2)) else 0

private theorem cut_symm (a b d U y : ℝ) : cut a b d U y = cut b a d U y := by
  simp only [cut,and_comm (a:= (y/d)^2+a^2 < U),Radial.angle,mul_comm a b,
    mul_comm ((y/d)^2+a^2) ((y/d)^2+b^2)]

private theorem sorted_cut (a b d U : ℝ) (hd : 0 < d) (hU : U ≤ (radiusSq:ℝ))
    (sum : a+b=1) (order : b ≤ a) :
    (∫ y in Ioi (0:ℝ), y^504 * cut a b d U y) ≤ 0 := by
  by_cases h : a^2 < U
  · have u1 : U < 1 := hU.trans_lt (by norm_num [radiusSq])
    have ha : 0 < a := by linarith
    have hb : 0 < b := by
      have h1 : a < 1 := by nlinarith [sq_nonneg (a-1)]
      linarith
    let Y := d*√(U-a^2)
    have hp : 0 < U-a^2 := sub_pos.mpr h
    have hy0 : 0 < Y := mul_pos hd (sqrt_pos.mpr hp)
    let g (y : ℝ) := y^504*sphericalKernel (Radial.angle a b ((y/d)^2))
    have eqn (y : ℝ) (hy : y ∈ Ioi 0) :
        y^504*cut a b d U y = (Iio Y).indicator g y := by
      have hpos : 0 ≤ y/d := div_nonneg hy.out.le hd.le
      have iff' : (y/d)^2+a^2 < U ↔ y < Y := by
        rw [← lt_sub_iff_add_lt,← lt_sqrt hpos,div_lt_iff₀ hd]
        dsimp [Y]; rw [mul_comm]
      have ha2 := pow_le_pow_left₀ hb.le order 2
      by_cases yes : y < Y
      · have h₁ := iff'.mpr yes
        rw [cut,ite_eq_left ⟨h₁,by linarith⟩,indicator_of_mem yes]
      · simp [cut,iff',yes]
    rw [setIntegral_congr_fun measurableSet_Ioi eqn,setIntegral_indicator measurableSet_Iio]
    rw [Ioi_inter_Iio,setIntegral_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le hy0.le]
    exact Radial.disk_nonpos ha hb hd sum order hU h
  · apply setIntegral_nonpos measurableSet_Ioi
    intro y _
    simp [cut,show ¬ (y/d)^2+a^2 < U by linarith [sq_nonneg (y/d)]]

private theorem cross_section (a b d U : ℝ) (hd : 0 < d) (hU : U ≤ (radiusSq:ℝ)) (sum : a+b=1) :
    (∫ v : F, cut a b d U ‖v‖) ≤ 0 := by
  have hr : (∫ y in Ioi (0:ℝ), y^504*cut a b d U y) ≤ 0 := by
    rcases le_total b a with h | h
    · exact sorted_cut a b d U hd hU sum h
    · simp_rw [cut_symm a b]
      exact sorted_cut b a d U hd hU (by linarith) h
  rw [integral_fun_norm_addHaar (E:=F) volume]
  simp only [finrank_euclideanSpace_fin,show 505-1 = 504 by decide,nsmul_eq_mul,smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg hr)

private def axis (d : ℝ) : W := WithLp.toLp 2 ((0:F),d)

private theorem axis_form {d R : ℝ} (hd : 0 < d) (hR : 0 < R) (v : F) (t : ℝ) :
    lens R (axis d) (WithLp.toLp 2 (v,t)) = cut ((t+d)/d) (-t/d) d (R^2/d^2) ‖v‖ := by
  let z : W := WithLp.toLp 2 (v,t)
  have hn : ‖z‖^2 = ‖v‖^2+t^2 := by simpa [z] using WithLp.prod_norm_sq_eq_of_L2 z
  have hm : ‖z+axis d‖^2 = ‖v‖^2+(t+d)^2 := by
    simpa [z,axis] using WithLp.prod_norm_sq_eq_of_L2 (z+axis d)
  have hi : ⟪z,z+axis d⟫ = ‖v‖^2+t*(t+d) := by
    change ⟪v,v+0⟫ + (t+d)*t = _
    rw [add_zero,real_inner_self_eq_norm_sq]; ring
  have e₁ : (‖v‖/d)^2+(-t/d)^2 = ‖z‖^2/d^2 := by rw [hn]; ring
  have e₂ : (‖v‖/d)^2+((t+d)/d)^2 = ‖z+axis d‖^2/d^2 := by rw [hm]; ring
  have h1 : ‖z‖ < R ↔ ‖z‖^2/d^2 < R^2/d^2 := by
    rw [div_lt_div_iff_of_pos_right (sq_pos_of_pos hd),sq_lt_sq₀ (norm_nonneg _) hR.le]
  have h2 : ‖z+axis d‖ < R ↔ ‖z+axis d‖^2/d^2 < R^2/d^2 := by
    rw [div_lt_div_iff_of_pos_right (sq_pos_of_pos hd),sq_lt_sq₀ (norm_nonneg _) hR.le]
  change (if ‖z‖ < R ∧ ‖z+axis d‖ < R then _ else _) = _
  simp only [cut,e₁,e₂,←h1,←h2,and_comm (a:=‖z+axis d‖ < R)]
  split_ifs
  · apply congrArg sphericalKernel
    rw [Radial.angle,e₁,e₂,sqrt_mul (by positivity),← div_pow,← div_pow,
      sqrt_sq (by positivity),sqrt_sq (by positivity)]
    rw [show (‖v‖/d)^2 - ((t+d)/d)*(-t/d) = ⟪z,z+axis d⟫/d^2 by rw [hi]; ring,
      show ‖z+axis d‖/d * (‖z‖/d) = (‖z‖*‖z+axis d‖)/d^2 by ring,
      div_div_div_cancel_right₀ (pow_ne_zero 2 hd.ne')]
  · rfl

/-- The actual lens sign, uniformly for every displacement at least s. -/
theorem physical_lens_nonpos {s : ℝ} (hs : 0 < s) (w : Space) (hw : s ≤ ‖w‖) :
    (∫ x, lens (√(radiusSq:ℝ)*s) w x) ≤ 0 := by
  let d := ‖w‖
  have hd : 0 < d := hs.trans_le hw
  let R := √(radiusSq:ℝ)*s
  have hsq : 0 < (radiusSq:ℝ) := by norm_num [radiusSq]
  have hR : 0 < R := mul_pos (sqrt_pos.mpr hsq) hs
  let e₀ := ChainState.windowCoord 505
  have he : ‖e₀ (axis d)‖ = ‖w‖ := by
    rw [e₀.norm_map,axis,WithLp.norm_toLp_snd,Real.norm_eq_abs,abs_of_pos hd]
  let e := e₀.trans (ℝ ∙ (e₀ (axis d)-w))ᗮ.reflection
  have eaxis : e (axis d) = w := Submodule.reflection_sub he
  let T := fun p : F × ℝ ↦ e (WithLp.toLp 2 p)
  have pres : MeasurePreserving T := e.measurePreserving.comp (WithLp.volume_preserving_toLp F ℝ)
  have memb : MeasurableEmbedding T := e.toHomeomorph.measurableEmbedding.comp
    (MeasurableEquiv.toLp 2 (F × ℝ)).measurableEmbedding
  have form (v : F) (t : ℝ) : lens R w (T (v,t)) = cut ((t+d)/d) (-t/d) d (R^2/d^2) ‖v‖ := by
    rw [← axis_form hd hR,← eaxis]
    simp only [T,lens,← map_add,e.norm_map,e.inner_map_map]
  have upper : R^2/d^2 ≤ (radiusSq:ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    dsimp only [R]; rw [mul_pow,sq_sqrt hsq.le]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hw 2) hsq.le
  rw [← pres.integral_comp memb (lens R w)]
  rw [Measure.volume_eq_prod,integral_prod_symm]
  · apply integral_nonpos
    intro t
    simp_rw [form]
    exact cross_section _ _ _ _ hd upper (by field_simp; ring)
  · exact (pres.integrable_comp_emb memb).2 (lens_integrable R w)

theorem thinShellSign : ThinShellSign := fun _ w hs hw _ ↦ physical_lens_nonpos hs w hw

theorem laterFloor_of_spherical (sphere : SphericalPairLower) : ControlledPlane.LaterDeterminantFloor :=
  laterFloor_of_sphere_shell sphere thinShellSign

end SigabaNeo.Wall1.HermiteWitness506

#print axioms SigabaNeo.Wall1.HermiteWitness506.physical_lens_nonpos
#print axioms SigabaNeo.Wall1.HermiteWitness506.thinShellSign
#print axioms SigabaNeo.Wall1.HermiteWitness506.laterFloor_of_spherical
