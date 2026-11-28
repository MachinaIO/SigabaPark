import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLensSlice506

set_option autoImplicit true

/-! From an extended slice to the radial integral on the physical disk. -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506.Radial
open Real Set MeasureTheory Metric

private def radial (a b d y : ℝ) := y^504 * sphericalKernel (angle a b ((y/d)^2))

private theorem radial_cont {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (d : ℝ) :
    Continuous (radial a b d) := by
  have h := (angle_cont ha hb).comp_continuous (f:=fun y : ℝ ↦ (y/d)^2)
    (by fun_prop) (fun y ↦ (show 0 ≤ (y/d)^2 from sq_nonneg _))
  exact (continuous_id.pow 504).mul (kernel_continuous.comp h)

private theorem extended_disk {a b p d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hab : (a-b)^2 ≤ 0.04^2) (hp : 1/(2*(1-(threshold:ℝ))) - 0.52^2 ≤ p)
    (endpt : angle a b p = angleMax) :
    (∫ y in (0:ℝ)..d*√p, radial a b d y) ≤ 0 := by
  obtain ⟨head,tail⟩ := extended_slice a b p ha.le hb.le hab hp endpt
  have pp : 0 < p := by norm_num [threshold] at hp; linarith
  let Y : ℝ := d*√p
  have hY : 0 < Y := mul_pos hd (sqrt_pos.mpr pp)
  let y (w : ℝ) := Y*exp (-w/505)
  let g := radial a b d
  have cg := radial_cont ha hb d
  have deriv (w : ℝ) : HasDerivAt y (-y w/505) w := by
    convert ((((hasDerivAt_id w).neg.div_const 505).exp).const_mul Y) using 1 <;>
      dsimp [y]; ring
  have eqn (w : ℝ) : ((y w)/d)^2 = p*exp (-2*w/505) := by
    dsimp [y,Y]
    rw [mul_assoc, mul_div_cancel_left₀ _ hd.ne',mul_pow,sq_sqrt pp.le,←exp_nat_mul]
    congr 2; push_cast; ring
  have sub := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=5) (g:=g)
    (fun w _ ↦ deriv w) (by dsimp [y]; fun_prop) cg
  have id' (w : ℝ) : (g ∘ y) w * (-y w/505) =
      (-Y^505/505) * (exp (-w) * sphericalKernel (profile a b p w)) := by
    dsimp only [Function.comp_apply,g,radial]
    rw [eqn]
    have h : y w ^ 505 = Y^505 * exp (-w) := by
      dsimp only [y]
      rw [mul_pow,← exp_nat_mul]
      congr 2; push_cast; ring
    unfold profile
    linear_combination -(sphericalKernel (angle a b (p*exp (-2*w/505))))/505 * h
  simp_rw [id'] at sub
  rw [intervalIntegral.integral_const_mul] at sub
  have y0 : y 0 = Y := by simp [y]
  rw [y0,intervalIntegral.integral_symm (y 5) Y] at sub
  have part : (∫ r in y 5..Y, g r) ≤ 0 := by
    have hh := mul_nonneg (by positivity : 0 ≤ Y^505/505) (neg_nonneg.mpr head.le)
    linarith
  have h5 : 0 < y 5 := mul_pos hY (exp_pos _)
  have pre : (∫ r in (0:ℝ)..y 5, g r) ≤ 0 := by
    rw [intervalIntegral.integral_of_le h5.le]
    apply setIntegral_nonpos measurableSet_Ioc
    intro r hr
    let w := -505*log (r/Y)
    have rpos := div_pos hr.1 hY
    have yw : y w = r := by
      dsimp [y,w]
      rw [show -(-505*log (r/Y))/505 = log (r/Y) by ring,exp_log rpos]
      field_simp
    have hw : 5 ≤ w := by
      have hr' : r/Y ≤ exp (-(5:ℝ)/505) :=
        (div_le_iff₀ hY).mpr (hr.2.trans_eq (mul_comm ..))
      have hl := log_le_log rpos hr'
      rw [log_exp] at hl
      dsimp [w]; linarith
    change r^504 * sphericalKernel (angle a b ((r/d)^2)) ≤ 0
    rw [← yw,eqn]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (tail w hw)
  rw [← intervalIntegral.integral_add_adjacent_intervals (cg.intervalIntegrable 0 (y 5))
    (cg.intervalIntegrable (y 5) Y)]
  exact add_nonpos pre part


private def cosSides (r s : ℝ) := (r^2+s^2-1)/(2*r*s)

private theorem cosSides_mono {r s r' s' : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ r') (hs' : s ≤ s') (hr1 : r' ≤ 1) (hs1 : s' ≤ 1) :
    cosSides r s ≤ cosSides r' s' := by
  have step {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hb1 : b ≤ 1) :
      cosSides a b ≤ cosSides c b := by
    have hc := ha.trans_le hac
    unfold cosSides
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have H := mul_nonneg (sub_nonneg.mpr hac) (show 0 ≤ a*c+1-b^2 by
      nlinarith [mul_nonneg ha.le hc.le,pow_le_pow_left₀ hb.le hb1 2])
    nlinarith only [mul_nonneg H hb.le]
  calc _ ≤ cosSides r' s := step hr hs hr' (hs'.trans hs1)
       _ = cosSides s r' := by unfold cosSides; ring
       _ ≤ cosSides s' r' := step hs (hr.trans_le hr') hs' hr1
       _ = _ := by unfold cosSides; ring

private theorem angle_sides {a b p : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hp : 0 ≤ p) (hab : a+b=1) :
    angle a b p = cosSides (√(p+a^2)) (√(p+b^2)) := by
  have h₁ : 0 ≤ p+a^2 := by positivity
  have h₂ : 0 ≤ p+b^2 := by positivity
  unfold angle cosSides
  rw [sqrt_mul h₁,sq_sqrt h₁,sq_sqrt h₂]
  have eq : p+a^2+(p+b^2)-1 = 2*(p-a*b) := by nlinarith [congrArg (·^2) hab]
  rw [eq]; ring

private theorem equal_sides {U : ℝ} (hu : 0 < U) :
    cosSides (√U) (√U) = 1-1/(2*U) := by
  unfold cosSides
  rw [sq_sqrt hu.le,mul_assoc,←sq,sq_sqrt hu.le]
  field_simp
  ring

private theorem far_sides : cosSides (√(radiusSq:ℝ)) (√((radiusSq:ℝ)-0.04)) ≤ threshold := by
  have h₁ : 0.9234 ≤ √(radiusSq:ℝ) := le_sqrt_of_sq_le (by norm_num [radiusSq])
  have h₂ : 0.9015 ≤ √((radiusSq:ℝ)-0.04) := le_sqrt_of_sq_le (by norm_num [radiusSq])
  unfold cosSides
  rw [sq_sqrt (by norm_num [radiusSq]),sq_sqrt (by norm_num [radiusSq])]
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul h₁ h₂ (by norm_num) (sqrt_nonneg _)
  norm_num [threshold,radiusSq] at hh ⊢
  linarith

/-- The radial integral on the original disk. The two normalized axial
distances sum to one and a is the larger one. -/
theorem disk_nonpos {a b d U : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (sum : a+b=1) (order : b ≤ a) (hU : U ≤ (radiusSq:ℝ)) (inside : a^2 < U) :
    (∫ y in (0:ℝ)..d*√(U-a^2), y^504 *
      sphericalKernel (angle a b ((y/d)^2))) ≤ 0 := by
  let P := U-a^2
  have hp : 0 < P := sub_pos.mpr inside
  have up : U ≤ 1 := hU.trans (by norm_num [radiusSq])
  have u0 : 0 < U := (sq_nonneg a).trans_lt inside
  have p0 : P+a^2 = U := by dsimp [P]; ring
  have hba := pow_le_pow_left₀ hb.le order 2
  let x := angle a b P
  let Y := d*√P
  have y0 : 0 ≤ Y := by dsimp [Y]; positivity
  have my (y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ Y) : (y/d)^2 ≤ P := by
    have h := (div_le_iff₀ hd).mpr (hy'.trans_eq (mul_comm ..))
    exact (pow_le_pow_left₀ (div_nonneg hy hd.le) h 2).trans_eq (sq_sqrt hp.le)
  have side := angle_sides ha hb hp.le sum
  rw [p0] at side
  have side2 : 0 < P+b^2 := by positivity
  have rpos := sqrt_pos.mpr u0
  have rpos2 := sqrt_pos.mpr side2
  have top := cosSides_mono rpos rpos2 le_rfl (sqrt_le_sqrt (show P+b^2 ≤ U by linarith))
    ((sqrt_le_left (by norm_num)).mpr (by linarith)) ((sqrt_le_left (by norm_num)).mpr (by linarith))
  rw [equal_sides u0,← side] at top
  by_cases ht : x ≤ (threshold:ℝ)
  · rw [intervalIntegral.integral_of_le y0]
    apply setIntegral_nonpos measurableSet_Ioc
    intro y hy
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    exact sub_nonpos.mpr ((angle_mono ha hb (mem_Ici.mpr (sq_nonneg (y/d))) hp.le (my y hy.1.le hy.2)).trans ht)
  have hit : (threshold:ℝ) < x := lt_of_not_ge ht
  have bal : a-b < 0.04 := by
    by_contra! h
    have hgap : 0.04 ≤ a^2-b^2 := by nlinarith [congrArg (fun t : ℝ ↦ t*(a-b)) sum]
    have hs := cosSides_mono rpos rpos2 (sqrt_le_sqrt hU)
      (sqrt_le_sqrt (show P+b^2 ≤ (radiusSq:ℝ)-0.04 by linarith))
      ((sqrt_le_left (by norm_num)).mpr (by norm_num [radiusSq]))
      ((sqrt_le_left (by norm_num)).mpr (by norm_num [radiusSq]))
    exact ht (side.le.trans (hs.trans far_sides))
  have t1 : 0 < 1-(threshold:ℝ) := by norm_num [threshold]
  have ls : 1/(2*(1-(threshold:ℝ))) ≤ U := by
    apply (div_le_iff₀ (by positivity)).mpr
    have H := (div_lt_iff₀ (show 0 < 2*U by positivity)).mp
      (show 1/(2*U) < 1-(threshold:ℝ) by dsimp [x] at hit; linarith)
    linarith
  have amin : a ≤ 0.52 := by linarith
  have Pmin : 1/(2*(1-(threshold:ℝ))) - 0.52^2 ≤ P := by
    dsimp [P]; linarith [pow_le_pow_left₀ ha.le amin 2]
  have rSq : 0 < (radiusSq:ℝ) := by norm_num [radiusSq]
  have edge : x ≤ angleMax := by
    have H := one_div_le_one_div_of_le (show 0 < 2*U by positivity)
      (show 2*U ≤ 2*(radiusSq:ℝ) by linarith)
    dsimp [angleMax,x]; linarith
  have a1 : a ≤ 1 := by linarith
  have b1 : b ≤ 1 := by linarith
  have s4 : angleMax ≤ angle a b 4 := by
    have h1' := pow_le_pow_left₀ ha.le a1 2
    have h2' := pow_le_pow_left₀ hb.le b1 2
    have h := mul_le_mul (show 4+a^2 ≤ 5 by linarith) (show 4+b^2 ≤ 5 by linarith)
      (by positivity : 0 ≤ 4+b^2) (by norm_num : (0:ℝ) ≤ 5)
    have H : √((4+a^2)*(4+b^2)) ≤ 5 := (sqrt_le_left (by norm_num)).mpr (by linarith)
    have ab := mul_le_mul a1 b1 hb.le zero_le_one
    unfold angle
    apply (le_div_iff₀ (by positivity)).mpr
    have hx : 0 ≤ angleMax ∧ angleMax ≤ 0.5 := by norm_num [angleMax,radiusSq]
    linarith [mul_le_mul hx.2 H (sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 0.5)]
  obtain ⟨p,hpI,ep⟩ := intermediate_value_Icc (show P ≤ 4 by dsimp [P]; linarith [sq_nonneg a])
    ((angle_cont ha hb).mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hp.le)))
    (show angleMax ∈ Icc (angle a b P) (angle a b 4) from ⟨edge,s4⟩)
  have hPY : Y ≤ d*√p := mul_le_mul_of_nonneg_left (sqrt_le_sqrt hpI.1) hd.le
  have extend := extended_disk ha hb hd (pow_le_pow_left₀ (sub_nonneg.mpr order) bal.le 2)
    (Pmin.trans hpI.1) ep
  have cg := radial_cont ha hb d
  rw [← intervalIntegral.integral_add_adjacent_intervals (cg.intervalIntegrable 0 Y)
    (cg.intervalIntegrable Y (d*√p))] at extend
  have save : 0 ≤ ∫ y in Y..d*√p, radial a b d y := by
    apply intervalIntegral.integral_nonneg hPY
    intro y hy
    have hscale := (le_div_iff₀ hd).mpr ((mul_comm ..).le.trans hy.1 : √P*d ≤ y)
    have hvalue : P ≤ (y/d)^2 := (sq_sqrt hp.le) ▸ pow_le_pow_left₀ (sqrt_nonneg P) hscale 2
    exact mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr (hit.le.trans
      (angle_mono ha hb hp.le (mem_Ici.mpr (sq_nonneg (y/d))) hvalue))) (sq_nonneg _))
  change (∫ y in (0:ℝ)..Y, radial a b d y) ≤ 0
  linarith

end SigabaNeo.Wall1.HermiteWitness506.Radial

#print axioms SigabaNeo.Wall1.HermiteWitness506.Radial.disk_nonpos
