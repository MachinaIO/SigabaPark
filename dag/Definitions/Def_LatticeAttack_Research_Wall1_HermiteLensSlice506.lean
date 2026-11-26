import Definitions.Def_LatticeAttack_Research_Wall1_HermiteLensRadial506

set_option autoImplicit true

/-! Angular derivative and signed radial integral of an extended transverse slice. -/

noncomputable section
namespace SigabaNeo.Wall1.HermiteWitness506.Radial
open Real Set MeasureTheory

/-- The parameter p is the squared transverse radius in separation-one units. -/
def angle (a b p : ℝ) := (p-a*b) / √((p+a^2)*(p+b^2))

def angleMax : ℝ := 1 - 1/(2*(radiusSq:ℝ))

private def speed (a b p : ℝ) :=
  (1-angle a b p ^ 2) * ((p+a*b)/√((p+a^2)*(p+b^2)))

private theorem scalar_deriv (a b : ℝ) {p : ℝ} (hp : 0 < p) :
    HasDerivAt (angle a b) (speed a b p / (2*p)) p := by
  let d := √((p+a^2)*(p+b^2))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd2 : d^2 = (p+a^2)*(p+b^2) := sq_sqrt (by positivity)
  have h1 := (hasDerivAt_id p).add_const (a^2)
  have h2 := (hasDerivAt_id p).add_const (b^2)
  have h3 := (h1.mul h2).sqrt (by dsimp; positivity)
  have h4 := ((hasDerivAt_id p).sub_const (a*b)).div h3 hd.ne'
  convert h4 using 1
  · rfl
  dsimp only [speed,angle]
  change (1-((p-a*b)/d)^2)*((p+a*b)/d)/(2*p) =
    (1*d - (p-a*b)*(_/(2*d)))/d^2
  field_simp [hd.ne',hp.ne']
  ring_nf at hd2 ⊢
  rw [hd2]
  simp only [id_eq]
  ring

private theorem controls (a b : ℝ) {p : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ speed a b p ∧ speed a b p ≤ 1 ∧
    ((a-b)^2 ≤ 0.04^2 → 0.5692 ≤ p →
      (1-angle a b p^2)*0.9985974 ≤ speed a b p ∧ speed a b p ≤ 1-angle a b p^2) := by
  let d := √((p+a^2)*(p+b^2))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd2 : d^2 = (p+a^2)*(p+b^2) := sq_sqrt (by positivity)
  have h1 : (p-a*b)^2 ≤ d^2 := by rw [hd2]; nlinarith [mul_nonneg hp.le (sq_nonneg (a+b))]
  have h2 : (p+a*b)^2 ≤ d^2 := by rw [hd2]; nlinarith [mul_nonneg hp.le (sq_nonneg (a-b))]
  have h3 : 0 ≤ 1-angle a b p ^ 2 := by
    unfold angle
    change 0 ≤ 1-((p-a*b)/d)^2
    rw [div_pow]; linarith [(div_le_one (sq_pos_of_pos hd)).mpr h1]
  have h4 : (p+a*b)/d ≤ 1 :=
    (div_le_one hd).mpr (le_of_sq_le_sq h2 hd.le)
  have h5 : 0 ≤ (p+a*b)/d := by positivity
  change 0 ≤ _*((p+a*b)/d) ∧ _*((p+a*b)/d) ≤ 1 ∧ _
  refine ⟨mul_nonneg h3 h5,(mul_le_mul_of_nonneg_left h4 h3).trans ?_,?_⟩
  · linarith [sq_nonneg (angle a b p)]
  intro he hp'
  have h6 : 0.9985974 ≤ (p+a*b)/d := by
    apply (le_div_iff₀ hd).mpr
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow,hd2]
    have extra := mul_le_mul_of_nonneg_left he hp.le
    have base : 0.5692*p ≤ (p+a*b)^2 := by
      have h := mul_le_mul_of_nonneg_right hp' hp.le
      have h' := mul_nonneg ha hb
      nlinarith [mul_nonneg h' hp.le,sq_nonneg (a*b)]
    nlinarith only [extra,base,hp.le]
  exact ⟨mul_le_mul_of_nonneg_left h6 h3,(mul_le_mul_of_nonneg_left h4 h3).trans_eq (mul_one _)⟩

theorem angle_cont {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (angle a b) (Ici 0) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro p hp
  exact (sqrt_pos.mpr (mul_pos (add_pos_of_nonneg_of_pos hp (sq_pos_of_pos ha))
    (add_pos_of_nonneg_of_pos hp (sq_pos_of_pos hb)))).ne'

theorem angle_mono {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : MonotoneOn (angle a b) (Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (angle_cont ha hb) (f':=fun p ↦ speed a b p/(2*p)) ?_ ?_
  · intro p hp
    rw [interior_Ici] at hp
    exact (scalar_deriv a b hp).hasDerivWithinAt
  · intro p hp
    rw [interior_Ici] at hp
    exact div_nonneg (controls a b hp ha.le hb.le).1 (mul_nonneg (by norm_num) hp.out.le)

/-- The physical angle along the logarithmic radius of an extended slice.
Here p is the squared transverse radius at the upper endpoint. -/
def profile (a b p w : ℝ) := angle a b (p*exp (-2*w/505))

private theorem profile_deriv (a b : ℝ) {p : ℝ} (hp : 0 < p) (w : ℝ) :
    HasDerivAt (profile a b p) (-speed a b (p*exp (-2*w/505))/505) w := by
  have e := ((((hasDerivAt_id w).const_mul (-2)).div_const 505).exp).const_mul p
  have he := (scalar_deriv a b (p:=p*exp (-2*w/505)) (by positivity)).comp w e
  convert he using 1
  · rfl
  dsimp only [id_eq,Function.comp_apply]
  field_simp [(exp_pos _).ne',hp.ne']

/-- The derivative controls prove the certified bin hypotheses from the endpoint
conditions of a transverse slice. This also identifies the nonpositive tail. -/
theorem extended_slice (a b p : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : (a-b)^2 ≤ 0.04^2)
    (hp : 1/(2*(1-(threshold:ℝ))) - 0.52^2 ≤ p)
    (endpt : angle a b p = angleMax) :
    (∫ w in (0:ℝ)..5, exp (-w)*sphericalKernel (profile a b p w)) < 0 ∧
      ∀ w : ℝ, 5 ≤ w → sphericalKernel (profile a b p w) ≤ 0 := by
  have pmin : 0.58 ≤ p := by norm_num [threshold] at hp; linarith
  have ppos : 0 < p := by linarith
  let f := profile a b p
  have hder := profile_deriv a b ppos
  have diff : Differentiable ℝ f := fun w ↦ (hder w).differentiableAt
  have h0 : f 0 = angleMax := by simpa [f,profile] using endpt
  have lo0 (w : ℝ) : -1/505 ≤ deriv f w := by
    rw [(hder w).deriv]
    linarith [(controls a b (p:=p*exp (-2*w/505)) (by positivity) ha hb).2.1]
  have hi0 (w : ℝ) : deriv f w ≤ 0 := by
    rw [(hder w).deriv]
    linarith [(controls a b (p:=p*exp (-2*w/505)) (by positivity) ha hb).1]
  have lim (w : ℝ) (hw : w ∈ Icc 0 5) :
      -0.836951/505 ≤ deriv f w ∧ deriv f w ≤ -0.827693/505 := by
    have p' : 0.5692 ≤ p*exp (-2*w/505) := by
      have h := Real.add_one_le_exp (-2*w/505)
      have h' : 1-10/505 ≤ exp (-2*w/505) := by linarith [hw.2]
      have low : 0.58078 ≤ p := by norm_num [threshold] at hp; linarith
      linarith [mul_le_mul low h' (by norm_num) ppos.le]
    have lc := mul_sub_le_image_sub_of_le_deriv diff lo0 hw.1
    have uc := image_sub_le_mul_sub_of_deriv_le diff hi0 hw.1
    rw [h0] at lc uc
    have bounds : 0.413695668 ≤ angleMax ∧ angleMax ≤ 0.413695669 := by norm_num [angleMax,radiusSq]
    have r1 : (0.40379467:ℝ) ≤ f w := by linarith [bounds.1,hw.2]
    have r2 : f w ≤ 0.413695669 := by linarith [bounds.2]
    have hc := (controls a b (p:=p*exp (-2*w/505)) (by positivity) ha hb).2.2 hab p'
    change (1-f w^2)*0.9985974 ≤ _ ∧ _ ≤ 1-f w^2 at hc
    rw [(hder w).deriv]
    constructor
    · nlinarith [pow_le_pow_left₀ (by norm_num) r1 2,hc.2]
    · nlinarith [pow_le_pow_left₀ (by linarith : 0 ≤ f w) r2 2,hc.1]
  have lo (w : ℝ) (hw : w ∈ Icc 0 5) :=
    (convex_Icc (0:ℝ) 5).mul_sub_le_image_sub_of_le_deriv diff.continuous.continuousOn
      diff.differentiableOn (fun u hu ↦ (lim u (interior_subset hu)).1) 0 (by constructor <;> norm_num) w hw hw.1
  have hi (w : ℝ) (hw : w ∈ Icc 0 5) :=
    (convex_Icc (0:ℝ) 5).image_sub_le_mul_sub_of_deriv_le diff.continuous.continuousOn
      diff.differentiableOn (fun u hu ↦ (lim u (interior_subset hu)).2) 0 (by constructor <;> norm_num) w hw hw.1
  have edge : 0.1108768 ≤ 100*(angleMax-(threshold:ℝ)) ∧
      100*(angleMax-(threshold:ℝ)) ≤ 0.1108769 := by norm_num [angleMax,threshold,radiusSq]
  constructor
  · apply integral_profile_neg f diff.continuous.continuousOn
    · intro w hw; have h := lo w hw; rw [h0] at h; linarith [edge.1]
    · intro w hw; have h := hi w hw; rw [h0] at h; linarith [edge.2]
  · intro w hw
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := hi 5 (by constructor <;> norm_num)
    rw [h0] at h
    change f w - _ ≤ 0
    linarith [image_sub_le_mul_sub_of_deriv_le diff hi0 hw,edge.2]

end SigabaNeo.Wall1.HermiteWitness506.Radial

#print axioms SigabaNeo.Wall1.HermiteWitness506.Radial.extended_slice
