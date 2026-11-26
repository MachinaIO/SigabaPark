module

public import Mathlib

set_option autoImplicit true

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace SigabaNeo.Rogers.Gram

/-- The reciprocal symmetric beta integral after the substitution t = 2u - 1. -/
def normalizer (p : ℝ) := (2 * 4 ^ p * beta (p + 1) (p + 1))⁻¹

def weight (p t : ℝ) : ℝ≥0∞ :=
  if t ∈ Ioo (-1) 1 then ENNReal.ofReal (normalizer p * (1 - t ^ 2) ^ p) else 0

theorem weight_integral {p : ℝ} (hp : -1 < p) : ∫⁻ t, weight p t = 1 := by
  have hi : (fun u : ℝ ↦ 2 * u - 1) '' univ = univ := by
    ext t
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨(t + 1) / 2, by ring⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ))
    (f := fun u ↦ 2 * u - 1) (f' := fun _ ↦ 2) MeasurableSet.univ
    (fun x _ ↦ by convert ((hasDerivAt_id x).const_mul 2 |>.sub_const 1).hasDerivWithinAt using 1 <;> simp)
    (fun x _ y _ h ↦ by dsimp at h; linarith) (weight p)
  rw [hi, setLIntegral_univ, setLIntegral_univ] at h
  rw [h, ← lintegral_betaPDF_eq_one (α := p + 1) (β := p + 1) (by linarith) (by linarith)]
  apply lintegral_congr
  intro u
  by_cases hu : 0 < u ∧ u < 1
  · have ht : 2 * u - 1 ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [weight, ite_eq_left ht, betaPDF_of_pos_lt_one hu.1 hu.2, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [show 1 - (2 * u - 1)^2 = 4 * u * (1-u) by ring,
      Real.mul_rpow (mul_nonneg (by norm_num) hu.1.le) (by linarith [hu.2]),
      Real.mul_rpow (by norm_num) hu.1.le]
    simp only [normalizer, add_sub_cancel_right, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 4) p),
      ne_of_gt (beta_pos (by linarith : 0 < p+1) (by linarith : 0 < p+1))]
  · have ht : 2 * u - 1 ∉ Ioo (-1 : ℝ) 1 := fun h ↦ hu ⟨by linarith [h.1], by linarith [h.2]⟩
    simp [weight, ht, betaPDF_eq, hu]

def det3 (a b c : ℝ) := 1 + 2*a*b*c - a^2 - b^2 - c^2

theorem det3_fiber (a b t : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1) :
    det3 a b (a*b + Real.sqrt ((1-a^2)*(1-b^2))*t) = (1-a^2)*(1-b^2)*(1-t^2) := by
  have hpos (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1-x^2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) (show 0 < 1+x by linarith [hx.1])]
  have h := Real.sq_sqrt (mul_pos (hpos a ha) (hpos b hb)).le
  unfold det3
  linear_combination -t^2 * h

private theorem interval_pos {x : ℝ} (h : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1-x^2 := by
  nlinarith [mul_pos (sub_pos.mpr h.2) (show 0 < 1+x by linarith [h.1])]

/-- Change of variables on one positive-determinant fiber for any nonnegative test. -/
theorem fiber_integral (a b p : ℝ) (ha : a ∈ Ioo (-1 : ℝ) 1) (hb : b ∈ Ioo (-1 : ℝ) 1)
    (F : ℝ → ℝ≥0∞) :
    let u := (1-a^2)*(1-b^2)
    ∫⁻ c in {c | 0 < det3 a b c}, ENNReal.ofReal (det3 a b c ^ p) * F c =
      ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (u ^ (p+1/2) * (1-t^2)^p) *
        F (a*b + Real.sqrt u*t) := by
  dsimp only
  let u := (1-a^2)*(1-b^2)
  have hu : 0 < u := mul_pos (interval_pos ha) (interval_pos hb)
  have hs := Real.sqrt_pos.2 hu
  let f := fun t : ℝ ↦ a*b + Real.sqrt u*t
  have hd (t : ℝ) : det3 a b (f t) = u*(1-t^2) := by
    unfold f u det3
    linear_combination -t^2 * Real.sq_sqrt hu.le
  have him : f '' Ioo (-1 : ℝ) 1 = {c | 0 < det3 a b c} := by
    ext c
    constructor
    · rintro ⟨t, ht, rfl⟩
      change 0 < det3 a b (f t)
      rw [hd]
      exact mul_pos hu (interval_pos ht)
    · intro hc
      let t := (c-a*b)/Real.sqrt u
      have he : f t = c := by dsimp [f,t]; field_simp [hs.ne']; ring
      refine ⟨t, ?_, he⟩
      change 0 < det3 a b c at hc
      rw [← he, hd] at hc
      have ht := pos_of_mul_pos_right hc hu.le
      constructor <;> nlinarith [sq_nonneg (t-1), sq_nonneg (t+1)]
  rw [← him, lintegral_image_eq_lintegral_abs_deriv_mul (f' := fun _ ↦ Real.sqrt u)
    measurableSet_Ioo (fun t _ ↦ by
      simpa [f] using (((hasDerivAt_id t).const_mul (Real.sqrt u)).const_add (a*b)).hasDerivWithinAt)
    (fun x _ y _ h ↦ by dsimp [f] at h; exact mul_left_cancel₀ hs.ne' (add_left_cancel h) )]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [abs_of_pos hs, hd, ← mul_assoc, ← ENNReal.ofReal_mul hs.le,
    Real.mul_rpow hu.le (interval_pos ht).le, Real.rpow_add hu,
    Real.sqrt_eq_rpow]
  dsimp [u,f]
  simp only [Real.sqrt_eq_rpow]
  congr 2
  ring

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Ambient n) 1

def uniform (n : ℕ) : Measure (Sphere n) :=
  let μ := (volume : Measure (Ambient n)).toSphere
  (μ univ)⁻¹ • μ

def PairLaw (n : ℕ) : Prop :=
  Measure.map (fun z : Sphere n × Sphere n ↦ inner ℝ (z.1 : Ambient n) (z.2 : Ambient n))
    ((uniform n).prod (uniform n)) = volume.withDensity (weight (((n:ℝ)-3)/2))

theorem uniform_probability {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (uniform n) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let μ := (volume : Measure (Ambient n)).toSphere
  have h : μ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)
  constructor
  exact ENNReal.inv_mul_cancel h (measure_ne_top μ univ)

open scoped Pointwise in
/-- The remaining scalar input can be expressed entirely as volumes of solid cones. -/
theorem pairLaw_of_coneVolumes {n : ℕ} (hn : 3 ≤ n)
    (h : ∀ (x : Sphere n) (s : Set ℝ), MeasurableSet s →
      ((volume : Measure (Ambient n)).toSphere univ)⁻¹ *
        (n * volume (Ioo (0:ℝ) 1 • (Subtype.val ''
          {y : Sphere n | inner ℝ (x : Ambient n) (y : Ambient n) ∈ s}))) =
        (volume.withDensity (weight (((n:ℝ)-3)/2))) s) : PairLaw n := by
  let := uniform_probability (n := n) (by omega)
  let f := fun z : Sphere n × Sphere n ↦ inner ℝ (z.1 : Ambient n) (z.2 : Ambient n)
  have hm : Measurable f := by dsimp [f]; fun_prop
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have he (x : Sphere n) : uniform n (Prod.mk x ⁻¹' (f ⁻¹' s)) =
      (volume.withDensity (weight (((n:ℝ)-3)/2))) s := by
    rw [uniform, Measure.smul_apply, Measure.toSphere_apply' _ (measurable_prodMk_left (hm hs))]
    have heq : Prod.mk x ⁻¹' (f ⁻¹' s) =
        {y : Sphere n | inner ℝ (x : Ambient n) (y : Ambient n) ∈ s} := rfl
    rw [heq]
    simpa using h x s hs
  simp_rw [he]
  simp

open scoped Pointwise in
def cone {n : ℕ} (x : Sphere n) (s : Set ℝ) : Set (Ambient n) :=
  Ioo (0 : ℝ) 1 • (Subtype.val '' {y : Sphere n | inner ℝ (x : Ambient n) (y : Ambient n) ∈ s})

/-- Orthogonal invariance reduces every cone section to a single prescribed pole. -/
theorem cone_volume_eq {n : ℕ} (x y : Sphere n) (s : Set ℝ) :
    volume (cone x s) = volume (cone y s) := by
  let e := (ℝ ∙ ((x : Ambient n) - y))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub
    ((mem_sphere_zero_iff_norm.mp x.property).trans (mem_sphere_zero_iff_norm.mp y.property).symm)
  have forward (u v : Sphere n) (T : Ambient n ≃ₗᵢ[ℝ] Ambient n) (h : T u = v)
      {z : Ambient n} (hz : z ∈ cone u s) : T z ∈ cone v s := by
    obtain ⟨r, hr, _, ⟨w, hw, rfl⟩, rfl⟩ := hz
    rw [map_smul]
    refine ⟨r, hr, T w, ⟨⟨T w, mem_sphere_zero_iff_norm.mpr ?_⟩, ?_, rfl⟩, rfl⟩
    · rw [T.norm_map]
      exact mem_sphere_zero_iff_norm.mp w.property
    · change inner ℝ (v : Ambient n) (T w) ∈ s
      rwa [← h, T.inner_map_map]
  have hset : cone x s = e ⁻¹' cone y s := by
    ext z
    exact ⟨forward x y e he, fun hz ↦ by
      simpa using forward y x e.symm (e.symm_apply_eq.mpr he.symm) hz⟩
  rw [hset]
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

theorem pairLaw_of_pole {n : ℕ} (hn : 3 ≤ n) (pole : Sphere n)
    (h : ∀ s : Set ℝ, MeasurableSet s →
      ((volume : Measure (Ambient n)).toSphere univ)⁻¹ * (n * volume (cone pole s)) =
        (volume.withDensity (weight (((n : ℝ) - 3) / 2))) s) : PairLaw n := by
  apply pairLaw_of_coneVolumes hn
  intro x s hs
  change _ * (_ * volume (cone x s)) = _
  rw [cone_volume_eq x pole s]
  exact h s hs

theorem cone_Ici_eq {n : ℕ} (pole : Sphere n) (t : ℝ) :
    cone pole (Ici t) = {z | 0 < ‖z‖ ∧ ‖z‖ < 1 ∧ t * ‖z‖ ≤ inner ℝ (pole : Ambient n) z} := by
  ext z
  constructor
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    change t ≤ inner ℝ (pole : Ambient n) (y : Ambient n) at hy
    simp only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
      mem_sphere_zero_iff_norm.mp y.property, mul_one, real_inner_smul_right]
    exact ⟨hr.1, hr.2, by nlinarith [mul_le_mul_of_nonneg_left hy hr.1.le]⟩
  · rintro ⟨hz, hz', ht⟩
    let y : Sphere n := ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (by
      simp [norm_smul, hz.ne'])⟩
    refine ⟨‖z‖, ⟨hz,hz'⟩, y, ⟨y, ?_, rfl⟩, ?_⟩
    · change t ≤ inner ℝ (pole : Ambient n) (‖z‖⁻¹ • z)
      rw [real_inner_smul_right, ← div_eq_inv_mul, le_div_iff₀ hz]
      exact ht
    · change ‖z‖ • (‖z‖⁻¹ • z) = z
      simp [smul_smul, hz.ne']

/-- Axial slice integral for a positive cap, omitting the transverse unit-ball volume. -/
def capSlice (d t : ℝ) : ℝ :=
  t / d * (1-t^2)^((d-1)/2) + ∫ u in t..1, (1-u^2)^((d-1)/2)

/-- Transverse volume of the section of the solid cap at an interior axial coordinate. -/
theorem capSection_volume (m : ℕ) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    volume {w : Ambient m | u^2 + ‖w‖^2 < 1 ∧ t * Real.sqrt (u^2 + ‖w‖^2) ≤ u} =
      ENNReal.ofReal (min (u * (Real.sqrt (1-t^2) / t)) (Real.sqrt (1-u^2))) ^ m *
        volume (Metric.ball (0 : Ambient m) 1) := by
  let a := u * (Real.sqrt (1-t^2) / t)
  let b := Real.sqrt (1-u^2)
  have hpos {x : ℝ} (h : x ∈ Ioo (0 : ℝ) 1) : 0 < 1-x^2 :=
    interval_pos ⟨by linarith [h.1], h.2⟩
  have ha : 0 < a := mul_pos hu.1 (div_pos (Real.sqrt_pos.2 (hpos ht)) ht.1)
  have hb : 0 < b := Real.sqrt_pos.2 (hpos hu)
  have hs : b^2 = 1-u^2 := Real.sq_sqrt (hpos hu).le
  have hc : (t*a)^2 = u^2*(1-t^2) := by
    dsimp [a]
    field_simp [ht.1.ne']
    nlinarith only [congrArg (u^2 * ·) (Real.sq_sqrt (hpos ht).le)]
  have cone (w : Ambient m) :
      t * Real.sqrt (u^2 + ‖w‖^2) ≤ u ↔ ‖w‖ ≤ a := by
    have hmul : t * ‖w‖ ≤ t * a ↔ ‖w‖ ≤ a := by exact mul_le_mul_iff_right₀ ht.1
    rw [← hmul, ← sq_le_sq₀ (mul_nonneg ht.1.le (Real.sqrt_nonneg _)) hu.1.le,
      ← sq_le_sq₀ (mul_nonneg ht.1.le (norm_nonneg _)) (mul_nonneg ht.1.le ha.le),
      mul_pow, Real.sq_sqrt (by positivity)]
    constructor <;> intro h <;> nlinarith only [hc, h]
  have ball (w : Ambient m) : u^2 + ‖w‖^2 < 1 ↔ ‖w‖ < b := by
    rw [← sq_lt_sq₀ (norm_nonneg _) hb.le]
    constructor <;> intro h <;> linarith only [hs, h]
  have hr := lt_min ha hb
  have upper := (volume : Measure (Ambient m)).addHaar_closedBall 0 hr.le
  have lower := (volume : Measure (Ambient m)).addHaar_ball_of_pos 0 hr
  change volume _ = ENNReal.ofReal (min a b) ^ m * _
  apply le_antisymm
  · calc
      _ ≤ volume (Metric.closedBall (0 : Ambient m) (min a b)) := by
        apply measure_mono
        intro w hw
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_min ((cone w).mp hw.2) ((ball w).mp hw.1).le
      _ = _ := by simpa [finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le] using upper
  · rw [finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le] at lower
    rw [← lower]
    apply measure_mono
    intro w hw
    rw [Metric.mem_ball, dist_zero_right, lt_min_iff] at hw
    exact ⟨(ball w).mpr hw.2, (cone w).mpr hw.1.le⟩

/-- Integrating the smaller of the cone and ball radii in transverse dimension m. -/
theorem capRadius_integral (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..1,
      min (u * (Real.sqrt (1-t^2) / t)) (Real.sqrt (1-u^2)) ^ m) =
      capSlice (m+1) t := by
  let k := Real.sqrt (1-t^2) / t
  have ht0 := ht.1
  have ht1 := ht.2
  have hk : 0 ≤ k := div_nonneg (Real.sqrt_nonneg _) ht0.le
  have cross : t * k = Real.sqrt (1-t^2) := by dsimp [k]; field_simp
  have radius (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
      Real.sqrt (1-u^2) ^ m = (1-u^2)^((m : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by nlinarith : 0 ≤ 1-u^2)]
    congr 1
    ring
  have hc : Continuous (fun u : ℝ ↦ min (u*k) (Real.sqrt (1-u^2)) ^ m) := by fun_prop
  change (∫ u in (0:ℝ)..1, min (u*k) (Real.sqrt (1-u^2)) ^ m) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 t)
    (hc.intervalIntegrable t 1)]
  have left : (∫ u in (0:ℝ)..t, min (u*k) (Real.sqrt (1-u^2)) ^ m) =
      ∫ u in (0:ℝ)..t, u^m * k^m := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht0.le] at hu
    dsimp only
    rw [min_eq_left, mul_pow]
    exact (mul_le_mul_of_nonneg_right hu.2 hk).trans (cross.le.trans
      (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (t-u), mul_nonneg hu.1 (sub_nonneg.mpr hu.2)])))
  have right : (∫ u in t..1, min (u*k) (Real.sqrt (1-u^2)) ^ m) =
      ∫ u in t..1, (1-u^2)^((m : ℝ)/2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht1.le] at hu
    dsimp only
    rw [min_eq_right, radius u (ht0.le.trans hu.1) hu.2]
    exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (u-t), mul_nonneg ht0.le (sub_nonneg.mpr hu.1)] : 1-u^2 ≤ 1-t^2)).trans
      (cross.ge.trans (mul_le_mul_of_nonneg_right hu.1 hk))
  rw [left, right, intervalIntegral.integral_mul_const, integral_pow]
  simp only [capSlice, add_sub_cancel_right, zero_pow (Nat.succ_ne_zero m), sub_zero]
  congr 1
  rw [pow_succ, ← radius t ht0.le ht1.le, ← cross, mul_pow]
  ring

/-- The positive solid cap volume in axial and transverse product coordinates. -/
theorem axialCap_volume (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    volume {z : ℝ × Ambient m | z.1 ∈ Ioo (0 : ℝ) 1 ∧
      z.1^2 + ‖z.2‖^2 < 1 ∧ t * Real.sqrt (z.1^2 + ‖z.2‖^2) ≤ z.1} =
      ENNReal.ofReal (capSlice (m+1) t) * volume (Metric.ball (0 : Ambient m) 1) := by
  let r := fun u : ℝ ↦ min (u * (Real.sqrt (1-t^2) / t)) (Real.sqrt (1-u^2))
  have hc : Continuous (fun u ↦ r u ^ m) := by dsimp [r]; fun_prop
  have hr (u : ℝ) (hu : 0 ≤ u) : 0 ≤ r u :=
    le_min (mul_nonneg hu (div_nonneg (Real.sqrt_nonneg _) ht.1.le)) (Real.sqrt_nonneg _)
  let V := volume (Metric.ball (0 : Ambient m) 1)
  rw [Measure.volume_eq_prod, Measure.prod_apply (by measurability)]
  have eq (u : ℝ) :
      volume ((Prod.mk u) ⁻¹' {z : ℝ × Ambient m | z.1 ∈ Ioo (0 : ℝ) 1 ∧
        z.1^2 + ‖z.2‖^2 < 1 ∧ t * Real.sqrt (z.1^2 + ‖z.2‖^2) ≤ z.1}) =
      (Ioo (0 : ℝ) 1).indicator (fun x ↦ ENNReal.ofReal (r x ^ m) * V) u := by
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simpa [preimage_ofPred_eq, hu, hu.1, hu.2, r, V, ENNReal.ofReal_pow (hr u hu.1.le)] using
        capSection_volume m ht hu
    · have h : ¬ (0 < u ∧ u < 1) := hu
      simp [preimage_ofPred_eq, hu, h]
  simp_rw [eq]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    lintegral_mul_const' _ _ measure_ball_lt_top.ne,
    ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le zero_le_one]
  · rw [← capRadius_integral m ht]
  · exact (hc.intervalIntegrable 0 1).1
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    exact pow_nonneg (hr u hu.1.le) m

/-- Ambient solid cap volume for any pole and an interior positive threshold. -/
theorem cone_positive_volume (m : ℕ) (pole : Sphere (m+1)) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    volume (cone pole (Ici t)) =
      ENNReal.ofReal (capSlice (m+1) t) * volume (Metric.ball (0 : Ambient m) 1) := by
  let F := Ambient m
  let E := WithLp 2 (ℝ × F)
  have hd : Module.finrank ℝ E = m+1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × F)).finrank_eq, Module.finrank_prod]
    simp [F, Nat.add_comm]
  let e := ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr
  let axis : E := WithLp.toLp 2 (1,0)
  let y : Sphere (m+1) := ⟨e axis, mem_sphere_zero_iff_norm.mpr (by
    rw [e.norm_map, WithLp.norm_toLp_fst]; norm_num)⟩
  let S := {z : ℝ × F | z.1 ∈ Ioo (0 : ℝ) 1 ∧
    z.1^2 + ‖z.2‖^2 < 1 ∧ t * Real.sqrt (z.1^2 + ‖z.2‖^2) ≤ z.1}
  have sets : e ⁻¹' cone y (Ici t) = WithLp.ofLp ⁻¹' S := by
    rw [cone_Ici_eq]
    ext z
    have hs := WithLp.prod_norm_sq_eq_of_L2 z
    simp only [Real.norm_eq_abs, sq_abs] at hs
    have hroot : Real.sqrt (z.fst^2 + ‖z.snd‖^2) = ‖z‖ := by
      rw [← hs, Real.sqrt_sq (norm_nonneg _)]
    have hi : inner ℝ axis z = z.fst := by
      change inner ℝ (WithLp.toLp 2 ((1 : ℝ), (0 : F))) z = _
      rw [WithLp.prod_inner_apply]
      simp
    change (0 < ‖e z‖ ∧ ‖e z‖ < 1 ∧ t * ‖e z‖ ≤ inner ℝ (e axis) (e z)) ↔
      z.fst ∈ Ioo (0 : ℝ) 1 ∧ z.fst^2 + ‖z.snd‖^2 < 1 ∧
        t * Real.sqrt (z.fst^2 + ‖z.snd‖^2) ≤ z.fst
    rw [e.inner_map_map, e.norm_map, hi, hroot, ← hs]
    constructor
    · rintro ⟨hz, hz1, h⟩
      exact ⟨⟨(mul_pos ht.1 hz).trans_le h, by nlinarith [sq_nonneg ‖z.snd‖]⟩,
        by nlinarith, h⟩
    · rintro ⟨hu, h, hc⟩
      exact ⟨by nlinarith [hu.1, norm_nonneg z, sq_nonneg ‖z.snd‖],
        by nlinarith [norm_nonneg z], hc⟩
  rw [cone_volume_eq pole y, ← e.measurePreserving.measure_preimage_emb
    e.toMeasurableEquiv.measurableEmbedding, sets,
    (WithLp.volume_preserving_ofLp ℝ F).measure_preimage_emb
      (MeasurableEquiv.toLp 2 (ℝ × F)).symm.measurableEmbedding]
  exact axialCap_volume m ht

private theorem capPower_integrable {p t : ℝ} (hp : -1 < p) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u : ℝ ↦ (1-u^2)^p) volume t 1 := by
  have h₁ : IntervalIntegrable (fun u : ℝ ↦ (1-u)^p) volume t 1 := by
    simpa using (intervalIntegral.intervalIntegrable_rpow' (a := 1-t) (b := 0) hp).comp_sub_left 1
  have h₂ : ContinuousOn (fun u : ℝ ↦ (1+u)^p) (uIcc t 1) := by
    apply (continuous_const.add continuous_id).continuousOn.rpow_const
    intro u hu
    rw [uIcc_of_le ht.2] at hu
    exact Or.inl (by change 1 + u ≠ 0; linarith [hu.1, ht.1])
  apply (h₁.mul_continuousOn h₂).congr
  intro u hu
  rw [uIoc_of_le ht.2] at hu
  dsimp
  rw [show 1-u^2 = (1-u)*(1+u) by ring, Real.mul_rpow (by linarith [hu.2]) (by linarith [ht.1, hu.1])]

theorem capSlice_derivative_of_two_le {d t : ℝ} (hd : 2 ≤ d) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (capSlice d) (-((d-1)/d) * (1-t^2)^((d-3)/2)) t := by
  let q := (d-1)/2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hc : Continuous (fun u : ℝ ↦ (1-u^2)^q) :=
    (continuous_const.sub (continuous_id.pow 2)).rpow_const fun _ ↦ Or.inr hq
  have hp : 0 < 1-t^2 := interval_pos ⟨by linarith [ht.1], ht.2⟩
  have hpow := (((hasDerivAt_id t).pow 2).const_sub 1).rpow_const (p := q) (Or.inl hp.ne')
  have hInt := intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable t 1)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert (((hasDerivAt_id t).div_const d).mul hpow).add hInt using 1 <;> try rfl
  dsimp
  have h : (1-t^2)^q = (1-t^2)^(q-1) * (1-t^2) := by
    convert Real.rpow_add_one hp.ne' (q-1) using 2; ring
  rw [h, show (d-3)/2 = q-1 by dsimp [q]; ring]
  field_simp [show d ≠ 0 by linarith]
  dsimp [q]
  ring

/-- The sliced cap is the tail integral of the unnormalized axial density. -/
theorem capSlice_tail_of_two_le {d t : ℝ} (hd : 2 ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    capSlice d t = ((d-1)/d) * ∫ u in t..1, (1-u^2)^((d-3)/2) := by
  have cont (q : ℝ) (hq : 0 ≤ q) : Continuous (fun u : ℝ ↦ (1-u^2)^q) :=
    (continuous_const.sub (continuous_id.pow 2)).rpow_const fun _ ↦ Or.inr hq
  have hc := cont ((d-1)/2) (by linarith)
  have hcont : Continuous (capSlice d) := by
    unfold capSlice
    apply Continuous.add ((continuous_id.div_const d).mul hc)
    simp_rw [intervalIntegral.integral_symm (a := (1:ℝ))]
    exact
      (intervalIntegral.continuous_primitive (μ := volume) hc.intervalIntegrable 1).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2 hcont.continuousOn
    (fun x hx ↦ capSlice_derivative_of_two_le hd ⟨ht.1.trans_lt hx.1, hx.2⟩)
    ((capPower_integrable (p := (d-3)/2) (by linarith) ht).const_mul _)
  rw [intervalIntegral.integral_const_mul] at h
  have he : capSlice d 1 = 0 := by
    simp [capSlice, Real.zero_rpow (by linarith : (d-1)/2 ≠ 0)]
  rw [he] at h
  linarith

/-- The normalized candidate cap mass, including the hemisphere and the empty endpoint. -/
theorem capSlice_normalized_of_two_le {d t : ℝ} (hd : 2 ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    (volume.withDensity (weight ((d-3)/2))) (Ici t) =
      ENNReal.ofReal (normalizer ((d-3)/2) * (d/(d-1)) * capSlice d t) := by
  let p := (d-3)/2
  have hp : -1 < p := by dsimp [p]; linarith
  have hn : 0 ≤ normalizer p := by
    unfold normalizer
    exact inv_nonneg.mpr (by positivity [beta_pos (by linarith : 0 < p+1) (by linarith : 0 < p+1)])
  let f := fun u : ℝ ↦ normalizer p * (1-u^2)^p
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).mp
    ((capPower_integrable hp ht).const_mul (normalizer p))
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc t 1)] f := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    exact mul_nonneg hn (Real.rpow_nonneg (by nlinarith [ht.1.trans hu.1.le, hu.2] : 0 ≤ 1-u^2) _)
  have hs : Ioo (-1 : ℝ) 1 ∩ Ioi t = Ioo t 1 := by
    ext u
    constructor
    · exact fun h ↦ ⟨h.2, h.1.2⟩
    · exact fun h ↦ ⟨⟨by linarith [h.1, ht.1], h.2⟩, h.1⟩
  rw [withDensity_apply _ measurableSet_Ici, ← restrict_Ioi_eq_restrict_Ici]
  have hw : weight p = (Ioo (-1 : ℝ) 1).indicator (fun u ↦ ENNReal.ofReal (f u)) := by
    funext u
    by_cases hu : u ∈ Ioo (-1 : ℝ) 1 <;> simp [weight, hu, f]
  change (∫⁻ u in Ioi t, weight p u) = _
  rw [hw]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo, hs,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hi hnn,
    ← intervalIntegral.integral_of_le ht.2, capSlice_tail_of_two_le hd ht]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  dsimp [p]
  field_simp [show d ≠ 0 by linarith, show d-1 ≠ 0 by linarith]

theorem capSlice_derivative {d t : ℝ} (hd : 3 ≤ d) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (capSlice d) (-((d-1)/d) * (1-t^2)^((d-3)/2)) t :=
  capSlice_derivative_of_two_le (by linarith) ht

theorem capSlice_tail {d t : ℝ} (hd : 3 ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    capSlice d t = ((d-1)/d) * ∫ u in t..1, (1-u^2)^((d-3)/2) :=
  capSlice_tail_of_two_le (by linarith) ht

theorem capSlice_normalized {d t : ℝ} (hd : 3 ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    (volume.withDensity (weight ((d-3)/2))) (Ici t) =
      ENNReal.ofReal (normalizer ((d-3)/2) * (d/(d-1)) * capSlice d t) :=
  capSlice_normalized_of_two_le (by linarith) ht

theorem pairLaw_of_capVolumes {n : ℕ} (hn : 3 ≤ n) (pole : Sphere n)
    (h : ∀ t : ℝ, ((volume : Measure (Ambient n)).toSphere univ)⁻¹ *
      (n * volume {z : Ambient n | 0 < ‖z‖ ∧ ‖z‖ < 1 ∧ t * ‖z‖ ≤ inner ℝ (pole : Ambient n) z}) =
      (volume.withDensity (weight (((n : ℝ)-3)/2))) (Ici t)) : PairLaw n := by
  let := uniform_probability (n := n) (by omega)
  let f := fun y : Sphere n ↦ inner ℝ (pole : Ambient n) (y : Ambient n)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have mass (s : Set ℝ) (hs : MeasurableSet s) :
      (Measure.map f (uniform n)) s = ((volume : Measure (Ambient n)).toSphere univ)⁻¹ *
        (n * volume (cone pole s)) := by
    rw [Measure.map_apply hf hs, uniform, Measure.smul_apply, Measure.toSphere_apply' _ (hf hs)]
    simp [cone, f, Set.preimage]
  have eq := Measure.ext_of_Ici ((uniform n).map f) (volume.withDensity (weight (((n : ℝ)-3)/2)))
    (fun t ↦ by rw [mass _ measurableSet_Ici, cone_Ici_eq]; exact h t)
  exact pairLaw_of_pole hn pole fun s hs ↦ (mass s hs).symm.trans (congrArg (· s) eq)

theorem normalizer_gamma {p : ℝ} (hp : -1 < p) :
    normalizer p = Real.Gamma (p + 1 + 1/2) / (Real.sqrt Real.pi * Real.Gamma (p+1)) := by
  have h := Real.Gamma_mul_Gamma_add_half (p+1)
  have he : 2 * (4 : ℝ)^p * (2 : ℝ)^(1-2*(p+1)) = 1 := by
    rw [show (4 : ℝ) = 2^(2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      mul_assoc, ← Real.rpow_add (by norm_num), show 2*p+(1-2*(p+1)) = -1 by ring]
    norm_num
  have g := Real.Gamma_pos_of_pos (by linarith : 0 < p+1)
  have gg := Real.Gamma_pos_of_pos (by linarith : 0 < 2*(p+1))
  unfold normalizer beta
  rw [← two_mul]
  field_simp
  rw [show (2*(p+1)+1)/2 = p+1+1/2 by ring, mul_assoc, h]
  linear_combination -(Real.Gamma (2*(p+1)) * Real.sqrt Real.pi) * he

theorem transverse_ball_volume_of_pos (m : ℕ) (hm : 1 ≤ m) :
    volume (Metric.ball (0 : Ambient m) 1) =
      ENNReal.ofReal (normalizer (((m:ℝ)+1-3)/2) * ((m+1)/m)) *
        volume (Metric.ball (0 : Ambient (m+1)) 1) := by
  have : NeZero m := ⟨by omega⟩
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul, Nat.cast_add, Nat.cast_one]
  rw [normalizer_gamma (by linarith), ← ENNReal.ofReal_mul (by positivity [Real.Gamma_pos_of_pos (by linarith : 0 < ((m:ℝ)+1-3)/2+1+1/2), Real.Gamma_pos_of_pos (by linarith : 0 < ((m:ℝ)+1-3)/2+1)])]
  congr 1
  rw [show ((m:ℝ)+1-3)/2+1 = m/2 by ring,
    show (m:ℝ)/2+1/2 = (m+1)/2 by ring, Real.Gamma_add_one (by positivity : (m:ℝ)/2 ≠ 0),
    Real.Gamma_add_one (by positivity : ((m:ℝ)+1)/2 ≠ 0), pow_succ]
  field_simp [Real.Gamma_pos_of_pos (by positivity : 0 < (m:ℝ)/2),
    Real.Gamma_pos_of_pos (by positivity : 0 < ((m:ℝ)+1)/2)]

theorem normalized_positive_cap_of_pos (m : ℕ) (hm : 1 ≤ m) (pole : Sphere (m+1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (uniform (m+1)).map (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) (Ici t) =
      (volume.withDensity (weight (((m:ℝ)+1-3)/2))) (Ici t) := by
  have hd : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) > 0 := by linarith
  have hf : Measurable (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) := by fun_prop
  rw [Measure.map_apply hf measurableSet_Ici, uniform, Measure.smul_apply,
    Measure.toSphere_apply' _ (hf measurableSet_Ici), Measure.toSphere_apply_univ]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  change (_ * volume (Metric.ball (0 : Ambient (m+1)) 1))⁻¹ *
    (_ * volume (cone pole (Ici t))) = _
  rw [cone_positive_volume m pole ht, transverse_ball_volume_of_pos m hm,
    capSlice_normalized_of_two_le (by linarith) ⟨ht.1.le, ht.2.le⟩, add_sub_cancel_right]
  let B := volume (Metric.ball (0 : Ambient (m+1)) 1)
  let d : ℝ≥0∞ := ↑(m+1 : ℕ)
  have hB : B ≠ 0 := (Metric.measure_ball_pos volume _ zero_lt_one).ne'
  have hB' : B ≠ ∞ := measure_ball_ne_top
  have hd0 : d ≠ 0 := by simp [d]
  have hd' : d ≠ ∞ := by simp [d]
  change (d*B)⁻¹ * (d * (_ * (_ * B))) = _
  rw [show ∀ a b : ℝ≥0∞, d * (a * (b * B)) = (d*B)*(b*a) by intros; ac_rfl,
    ← mul_assoc, ENNReal.inv_mul_cancel (mul_ne_zero hd0 hB)
      (ENNReal.mul_ne_top hd' hB'), one_mul, ← ENNReal.ofReal_mul]
  have hg := Real.Gamma_pos_of_pos (by linarith : 0 < ((m:ℝ)+1-3)/2+1)
  rw [normalizer_gamma (by linarith)]
  positivity [Real.Gamma_pos_of_pos (by linarith : 0 < ((m:ℝ)+1-3)/2+1+1/2)]

private theorem positive_open_cap (m : ℕ) (hm : 1 ≤ m) (pole : Sphere (m+1))
    {t : ℝ} (ht : 0 ≤ t) :
    (uniform (m+1)).map (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) (Ioi t) =
      (volume.withDensity (weight (((m:ℝ)+1-3)/2))) (Ioi t) := by
  by_cases h : t < 1
  · obtain ⟨u, hu, hm', hl⟩ := exists_seq_strictAnti_tendsto' h
    have hs : (⋃ i, Ici (u i)) = Ioi t := by
      ext x
      simp only [mem_iUnion, mem_Ici, mem_Ioi]
      exact ⟨fun ⟨i, hi⟩ ↦ (hm' i).1.trans_le hi, fun hx ↦
        ((hl.eventually_lt_const hx).exists.imp fun i hi ↦ hi.le)⟩
    have mono : Monotone (fun i ↦ Ici (u i)) := fun _ _ hij ↦ Ici_subset_Ici.mpr (hu.antitone hij)
    rw [← hs, mono.measure_iUnion, mono.measure_iUnion]
    exact iSup_congr fun i ↦ normalized_positive_cap_of_pos m hm pole ⟨ht.trans_lt (hm' i).1, (hm' i).2⟩
  · have hf : Measurable (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) := by fun_prop
    rw [Measure.map_apply hf measurableSet_Ioi, withDensity_apply _ measurableSet_Ioi]
    have hs : (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) ⁻¹' Ioi t = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hb := real_inner_le_norm (pole : Ambient (m+1)) (y : Ambient (m+1))
      rw [mem_sphere_zero_iff_norm.mp pole.property, mem_sphere_zero_iff_norm.mp y.property] at hb
      change t < _ at hy
      linarith
    rw [hs, measure_empty]
    symm
    apply setLIntegral_eq_zero measurableSet_Ioi
    intro x hx
    simp [weight, show x ∉ Ioo (-1 : ℝ) 1 from fun hh ↦ h ((show t < x from hx).trans hh.2)]

theorem pole_law_of_pos (m : ℕ) (hm : 1 ≤ m) (pole : Sphere (m+1)) :
    (uniform (m+1)).map (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) =
      volume.withDensity (weight (((m:ℝ)+1-3)/2)) := by
  let p := (((m:ℝ)+1-3)/2)
  let ν := volume.withDensity (weight p)
  let f (q : Sphere (m+1)) := fun y : Sphere (m+1) ↦ inner ℝ (q : Ambient (m+1)) y
  have hf (q) : Measurable (f q) := by dsimp [f]; fun_prop
  let μ (q) := (uniform (m+1)).map (f q)
  have := uniform_probability (n := m+1) (by omega)
  have hprob (q : Sphere (m+1)) : IsProbabilityMeasure (μ q) := ⟨by simp [μ, Measure.map_apply (hf q)]⟩
  have hd : (1:ℝ) ≤ m := by exact_mod_cast hm
  have : IsProbabilityMeasure ν := ⟨by
    change volume.withDensity (weight p) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, weight_integral]
    dsimp [p]; linarith⟩
  change μ pole = ν
  apply Measure.ext_of_Ici
  intro t
  by_cases ht : 0 < t
  · obtain ⟨u, hu, hm', hl⟩ := exists_seq_strictMono_tendsto' ht
    have hs : (⋂ i, Ioi (u i)) = Ici t := by
      ext x
      simp only [mem_iInter, mem_Ioi, mem_Ici]
      exact ⟨fun h ↦ le_of_tendsto hl (Filter.Eventually.of_forall fun i ↦ (h i).le),
        fun h i ↦ (hm' i).2.trans_le h⟩
    have anti : Antitone (fun i ↦ Ioi (u i)) := fun _ _ hij ↦ Ioi_subset_Ioi (hu.monotone hij)
    have mass (ρ : Measure ℝ) [IsFiniteMeasure ρ] := anti.measure_iInter
      (μ := ρ) (fun _ ↦ measurableSet_Ioi.nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
    rw [← hs, mass, mass]
    exact iInf_congr fun i ↦ positive_open_cap m hm pole (hm' i).1.le
  · let q : Sphere (m+1) := ⟨-(pole : Ambient (m+1)), mem_sphere_zero_iff_norm.mpr
        (by simp [mem_sphere_zero_iff_norm.mp pole.property])⟩
    have he : μ pole (Iio t) = μ q (Ioi (-t)) := by
      simp only [μ, Measure.map_apply (hf _) measurableSet_Iio,
        Measure.map_apply (hf _) measurableSet_Ioi]
      congr 1
      ext y
      simp [f, q]
    have hn : ν (Iio t) = ν (Ioi (-t)) := by
      simp only [ν, withDensity_apply _ measurableSet_Iio, withDensity_apply _ measurableSet_Ioi]
      have hh := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
        (Homeomorph.neg ℝ).measurableEmbedding (weight p) (Ioi (-t))
      simpa [Iio, weight, Set.preimage, and_comm, neg_lt, neg_sq, Function.comp_def,
        show (fun a : ℝ ↦ -a) ⁻¹' Ioi (-t) = Iio t by ext; simp] using hh
    rw [← compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _),
      measure_compl measurableSet_Iio (measure_ne_top _ _), he, hn]
    simp only [measure_univ]
    rw [show μ q (Ioi (-t)) = ν (Ioi (-t)) from positive_open_cap m hm q (by linarith)]

theorem transverse_ball_volume (m : ℕ) (hm : 2 ≤ m) :
    volume (Metric.ball (0 : Ambient m) 1) =
      ENNReal.ofReal (normalizer (((m:ℝ)+1-3)/2) * ((m+1)/m)) *
        volume (Metric.ball (0 : Ambient (m+1)) 1) :=
  transverse_ball_volume_of_pos m (by omega)

theorem normalized_positive_cap (m : ℕ) (hm : 2 ≤ m) (pole : Sphere (m+1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (uniform (m+1)).map (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) (Ici t) =
      (volume.withDensity (weight (((m:ℝ)+1-3)/2))) (Ici t) :=
  normalized_positive_cap_of_pos m (by omega) pole ht

theorem pole_law (m : ℕ) (hm : 2 ≤ m) (pole : Sphere (m+1)) :
    (uniform (m+1)).map (fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y) =
      volume.withDensity (weight (((m:ℝ)+1-3)/2)) :=
  pole_law_of_pos m (by omega) pole

/-- In each transverse slice, radial weighting leaves the direction uniform. -/
theorem transverse_slice_integral (m : ℕ) (hm : 0 < m)
    (R : Ioi (0 : ℝ) → ℝ≥0∞) (hR : Measurable R)
    (F : Sphere m → ℝ≥0∞) (hF : Measurable F) :
    let e := homeomorphUnitSphereProd (Ambient m)
    (∫⁻ w, R (e w).2 * F (e w).1 ∂(volume : Measure (Ambient m)).comap Subtype.val) =
      (∫⁻ w, R (e w).2 ∂(volume : Measure (Ambient m)).comap Subtype.val) *
        ∫⁻ v, F v ∂uniform m := by
  let σ := (volume : Measure (Ambient m)).toSphere
  have h := (volume : Measure (Ambient m)).measurePreserving_homeomorphUnitSphereProd
  have h₁ := h.lintegral_comp (f := fun z : Sphere m × Ioi (0 : ℝ) ↦ R z.2 * F z.1)
    ((hR.comp measurable_snd).mul (hF.comp measurable_fst))
  have h₂ := h.lintegral_comp (f := fun z : Sphere m × Ioi (0 : ℝ) ↦ R z.2) (hR.comp measurable_snd)
  dsimp only
  rw [h₁, h₂, lintegral_prod (fun z : Sphere m × Ioi (0 : ℝ) ↦ R z.2 * F z.1)
      ((hR.comp measurable_snd).mul (hF.comp measurable_fst)).aemeasurable,
    lintegral_prod (fun z : Sphere m × Ioi (0 : ℝ) ↦ R z.2) (hR.comp measurable_snd).aemeasurable]
  simp_rw [lintegral_mul_const _ hR, lintegral_const_mul _ hF]
  rw [lintegral_const, uniform, lintegral_smul_measure]
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hσ : σ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero _)
  change _ = ((_ * σ univ) * ((σ univ)⁻¹ * _))
  rw [mul_assoc, ← mul_assoc (σ univ), ENNReal.mul_inv_cancel hσ (measure_ne_top _ _), one_mul]

/-- In solid-ball coordinates the normalized axial coordinate and transverse direction
factor for arbitrary measurable nonnegative tests. -/
theorem ball_axial_direction (m : ℕ) (hm : 0 < m)
    (A : ℝ → ℝ≥0∞) (hA : Measurable A) (F : Sphere m → ℝ≥0∞) (hF : Measurable F) :
    let e := homeomorphUnitSphereProd (Ambient m)
    let W := fun u r : ℝ ↦ if u^2 + r^2 < 1 then A (u / Real.sqrt (u^2 + r^2)) else 0
    let ν := (volume : Measure (Ambient m)).comap Subtype.val
    (∫⁻ u : ℝ, ∫⁻ w, W u (e w).2 * F (e w).1 ∂ν) =
      (∫⁻ u : ℝ, ∫⁻ w, W u (e w).2 ∂ν) * ∫⁻ v, F v ∂uniform m := by
  intro e W ν
  have hW : Measurable (fun z : ℝ × Ioi (0 : ℝ) ↦ W z.1 z.2) := by
    dsimp [W]
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (hA.comp (by fun_prop)) measurable_const
  have hs (u : ℝ) := transverse_slice_integral m hm _ (hW.comp
    (measurable_const.prodMk measurable_id : Measurable (fun r : Ioi (0 : ℝ) ↦ (u,r)))) F hF
  change ∀ u : ℝ, (∫⁻ w, W u (e w).2 * F (e w).1 ∂ν) = (∫⁻ w, W u (e w).2 ∂ν) * ∫⁻ v, F v ∂uniform m at hs
  simp_rw [hs]
  apply lintegral_mul_const
  have hmape := (volume : Measure (Ambient m)).measurePreserving_homeomorphUnitSphereProd
  have : SigmaFinite ν := SigmaFinite.of_map ν e.measurable.aemeasurable (by
    rw [show ν.map e = _ from hmape.map_eq]
    infer_instance)
  apply Measurable.lintegral_prod_right' (f := fun z ↦ W z.1 (e z.2).2)
  exact hW.comp (measurable_fst.prodMk
    ((measurable_snd.comp e.continuous.measurable).comp measurable_snd))

/-- Cosine law in a radially weighted transverse slice, for a fixed transverse pole. -/
theorem transverse_slice_cosine (m : ℕ) (hm : 1 ≤ m) (pole : Sphere (m+1))
    (R : Ioi (0 : ℝ) → ℝ≥0∞) (hR : Measurable R) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    let e := homeomorphUnitSphereProd (Ambient (m+1))
    (∫⁻ w, R (e w).2 * G (inner ℝ (pole : Ambient (m+1)) ((e w).1 : Ambient (m+1)))
      ∂(volume : Measure (Ambient (m+1))).comap Subtype.val) =
      (∫⁻ w, R (e w).2 ∂(volume : Measure (Ambient (m+1))).comap Subtype.val) *
        ∫⁻ t, G t ∂volume.withDensity (weight (((m:ℝ)+1-3)/2)) := by
  let f := fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) (y : Ambient (m+1))
  have hf : Measurable f := by dsimp [f]; fun_prop
  rw [← pole_law_of_pos m hm pole, lintegral_map hG hf]
  exact transverse_slice_integral (m+1) (by omega) R hR (G ∘ f) (hG.comp hf)

theorem pair_law {n : ℕ} (hn : 3 ≤ n) : PairLaw n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply pairLaw_of_coneVolumes hn
  intro x s hs
  have hf : Measurable (fun y : Sphere (m+1) ↦ inner ℝ (x : Ambient (m+1)) y) := by fun_prop
  have h := congrArg (fun μ : Measure ℝ ↦ μ s) (pole_law m (by omega) x)
  simp only [Measure.map_apply hf hs, uniform, Measure.smul_apply,
    Measure.toSphere_apply' _ (hf hs), finrank_euclideanSpace_fin, smul_eq_mul] at h
  simpa only [Set.preimage, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using h

theorem axial_pair_law (m : ℕ) (hm : 2 ≤ m) (pole : Sphere (m+1)) :
    let f := fun y : Sphere (m+1) ↦ inner ℝ (pole : Ambient (m+1)) y
    let ν := volume.withDensity (weight (((m:ℝ)+1-3)/2))
    ((uniform (m+1)).prod (uniform (m+1))).map (Prod.map f f) = ν.prod ν := by
  dsimp only
  have := uniform_probability (n := m+1) (by omega)
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), pole_law m hm pole]


def tripleWeight (n : ℕ) (x : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
  let (a,b,c) := x
  let p := ((n:ℝ)-4)/2
  if a ∈ Ioo (-1 : ℝ) 1 ∧ b ∈ Ioo (-1 : ℝ) 1 ∧ 0 < det3 a b c then
    ENNReal.ofReal (normalizer (p+1/2)^2 * normalizer p * det3 a b c ^ p)
  else 0

private theorem normalizer_pos {p : ℝ} (hp : -1 < p) : 0 < normalizer p := by
  unfold normalizer
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
    (beta_pos (by linarith) (by linarith)))

def angularThird (a b t : ℝ) := a*b + Real.sqrt ((1-a^2)*(1-b^2))*t

theorem transverse_inner {n : ℕ} (x y z : Sphere n) :
    let a := inner ℝ (x : Ambient n) y
    let b := inner ℝ (x : Ambient n) z
    let u := (y : Ambient n) - a • (x : Ambient n)
    let v := (z : Ambient n) - b • (x : Ambient n)
    inner ℝ (y : Ambient n) z =
      angularThird a b (inner ℝ (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)) := by
  dsimp only
  generalize ha : inner ℝ (x : Ambient n) y = a
  generalize hb : inner ℝ (x : Ambient n) z = b
  let u := (y : Ambient n) - a • (x : Ambient n)
  let v := (z : Ambient n) - b • (x : Ambient n)
  have unit (w : Sphere n) : inner ℝ (w : Ambient n) w = 1 := by
    simp [mem_sphere_zero_iff_norm.mp w.property]
  have normResidual (w : Sphere n) (c : ℝ) (hc : inner ℝ (x : Ambient n) w = c) :
      ‖(w : Ambient n) - c • (x : Ambient n)‖^2 = 1-c^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      unit, hc, (real_inner_comm _ _).trans hc]
    ring
  have hu : ‖u‖^2 = 1-a^2 := normResidual _ _ ha
  have hv : ‖v‖^2 = 1-b^2 := normResidual _ _ hb
  have huv : inner ℝ u v = inner ℝ (y : Ambient n) z - a*b := by
    simp only [u, v, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      unit, (real_inner_comm _ _).trans ha, hb]
    ring
  change _ = angularThird a b (inner ℝ (‖u‖⁻¹ • u) (‖v‖⁻¹ • v))
  rw [angularThird, ← hu, ← hv, ← mul_pow, Real.sqrt_sq (by positivity)]
  by_cases h : u = 0
  · simp [h] at huv ⊢
    linarith
  by_cases k : v = 0
  · simp [k] at huv ⊢
    linarith
  rw [real_inner_smul_left, real_inner_smul_right, huv]
  field_simp [norm_ne_zero_iff.mpr h, norm_ne_zero_iff.mpr k]
  ring

theorem triple_fiber_test (n : ℕ) (hn : 3 ≤ n) (a b : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    let p := ((n : ℝ)-4)/2
    ∫⁻ c, tripleWeight n (a,b,c) * F c =
      weight (p+1/2) a * weight (p+1/2) b *
        ∫⁻ t, weight p t * F (angularThird a b t) := by
  let p := ((n : ℝ)-4)/2
  have hp : -1 < p := by
    dsimp [p]
    have : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN := (normalizer_pos hp).le
  have hM := (normalizer_pos (show -1 < p+1/2 by linarith)).le
  dsimp only
  by_cases ha : a ∈ Ioo (-1 : ℝ) 1
  · by_cases hb : b ∈ Ioo (-1 : ℝ) 1
    · let u := (1-a^2)*(1-b^2)
      have hu : 0 < u := mul_pos (interval_pos ha) (interval_pos hb)
      let K := normalizer (p+1/2)^2 * normalizer p
      have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hN
      have hd : (fun c ↦ tripleWeight n (a,b,c) * F c) =
          {c | 0 < det3 a b c}.indicator
          (fun c ↦ ENNReal.ofReal K * (ENNReal.ofReal (det3 a b c ^ p) * F c)) := by
        funext c
        by_cases hc : 0 < det3 a b c <;>
          simp only [tripleWeight, ha, hb, hc, indicator, mem_ofPred_eq, and_self, and_false, ite_true, ite_false, zero_mul]
        change ENNReal.ofReal (K * _) * _ = _
        rw [ENNReal.ofReal_mul hK, mul_assoc]
      have ht : (fun t ↦ weight p t * F (angularThird a b t)) =
          (Ioo (-1 : ℝ) 1).indicator (fun t ↦ ENNReal.ofReal (normalizer p) *
            (ENNReal.ofReal ((1-t^2)^p) * F (angularThird a b t))) := by
        funext t
        by_cases h : t ∈ Ioo (-1 : ℝ) 1 <;>
          simp [weight, h, indicator, ENNReal.ofReal_mul hN, mul_assoc]
      change _ = weight (p+1/2) a * weight (p+1/2) b * _
      rw [hd, ht, lintegral_indicator (isOpen_lt continuous_const (by unfold det3; fun_prop)).measurableSet,
        lintegral_indicator measurableSet_Ioo, lintegral_const_mul'' _ (by unfold det3; fun_prop),
        fiber_integral a b p ha hb F, lintegral_const_mul'' _ (by unfold angularThird; fun_prop)]
      simp only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos (mul_pos (interval_pos ha) (interval_pos hb)) (p+1/2)).le, mul_assoc]
      rw [lintegral_const_mul'' _ (by fun_prop), weight, ite_eq_left ha, weight, ite_eq_left hb]
      dsimp [K]
      rw [ENNReal.ofReal_mul (sq_nonneg _), Real.mul_rpow (interval_pos ha).le (interval_pos hb).le,
        ENNReal.ofReal_mul (Real.rpow_pos_of_pos (interval_pos ha) _).le]
      simp only [sq, ENNReal.ofReal_mul hM, angularThird]
      ac_rfl
    · simp [tripleWeight, weight, hb]
  · simp [tripleWeight, weight, ha]

/-- Integrating out the third coordinate gives the independent first two marginals. -/
theorem triple_marginal (n : ℕ) (hn : 3 ≤ n) (a b : ℝ) :
    ∫⁻ c, tripleWeight n (a,b,c) =
      weight (((n:ℝ)-4)/2+1/2) a * weight (((n:ℝ)-4)/2+1/2) b := by
  have hp : -1 < ((n : ℝ)-4)/2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simpa [weight_integral hp] using triple_fiber_test n hn a b (fun _ ↦ 1) measurable_const

private theorem measurable_tripleWeight (n : ℕ) : Measurable (tripleWeight n) := by
  unfold tripleWeight det3
  dsimp only
  apply Measurable.ite _ (by fun_prop) measurable_const
  change MeasurableSet ((Prod.fst ⁻¹' Ioo (-1:ℝ) 1) ∩
    ((fun x : ℝ × ℝ × ℝ ↦ x.2.1) ⁻¹' Ioo (-1:ℝ) 1 ∩ {x | 0 < det3 x.1 x.2.1 x.2.2}))
  apply MeasurableSet.inter (measurable_fst measurableSet_Ioo)
  apply MeasurableSet.inter ((measurable_fst.comp measurable_snd) measurableSet_Ioo)
  exact measurableSet_lt (f := fun _ ↦ (0 : ℝ))
    (g := fun x : ℝ × ℝ × ℝ ↦ det3 x.1 x.2.1 x.2.2) measurable_const (by unfold det3; fun_prop)

theorem triple_integral (n : ℕ) (hn : 3 ≤ n) : ∫⁻ x, tripleWeight n x = 1 := by
  have hm := measurable_tripleWeight n
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  have h (a : ℝ) : Measurable (fun y : ℝ × ℝ ↦ tripleWeight n (a,y)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  simp_rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ), lintegral_prod _ (h _).aemeasurable,
    triple_marginal n hn]
  have hw : Measurable (weight (((n:ℝ)-4)/2+1/2)) := by unfold weight; exact Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const
  have hp : -1 < ((n:ℝ)-4)/2+1/2 := by
    have : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp_rw [lintegral_const_mul'' _ hw.aemeasurable, weight_integral hp, mul_one]
  exact weight_integral hp

def TripleLaw (n : ℕ) : Prop :=
  Measure.map (fun z : Sphere n × Sphere n × Sphere n ↦
    (inner ℝ (z.1 : Ambient n) (z.2.1 : Ambient n),
     inner ℝ (z.1 : Ambient n) (z.2.2 : Ambient n),
     inner ℝ (z.2.1 : Ambient n) (z.2.2 : Ambient n)))
    ((uniform n).prod ((uniform n).prod (uniform n))) = volume.withDensity (tripleWeight n)

/-- Sampling identity for the three angles before changing transverse coordinate. -/
def AngularDisintegration (n : ℕ) : Prop :=
  ∀ F : ℝ × ℝ × ℝ → ℝ≥0∞, Measurable F →
    let p := ((n : ℝ)-4)/2
    (∫⁻ z : Sphere n × Sphere n × Sphere n,
      F (inner ℝ (z.1 : Ambient n) (z.2.1 : Ambient n),
         inner ℝ (z.1 : Ambient n) (z.2.2 : Ambient n),
         inner ℝ (z.2.1 : Ambient n) (z.2.2 : Ambient n))
      ∂(uniform n).prod ((uniform n).prod (uniform n))) =
      ∫⁻ a, ∫⁻ b, weight (p+1/2) a * weight (p+1/2) b *
        ∫⁻ t, weight p t * F (a,b,angularThird a b t)

/-- The unit ball gives the uniform sphere law after radial normalization. -/
theorem ball_normalized_integral (n : ℕ) (hn : 0 < n)
    (F : Ambient n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v in Metric.ball (0 : Ambient n) 1, F (‖v‖⁻¹ • v)) =
      volume (Metric.ball (0 : Ambient n) 1) * ∫⁻ v : Sphere n, F v ∂uniform n := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let R := fun r : Ioi (0 : ℝ) ↦ if (r : ℝ) < 1 then (1 : ℝ≥0∞) else 0
  have hR : Measurable R := Measurable.ite (measurableSet_lt measurable_subtype_coe
    measurable_const) measurable_const measurable_const
  have h := transverse_slice_integral n hn R hR (fun v ↦ F v) (hF.comp measurable_subtype_coe)
  let B := Metric.ball (0 : Ambient n) 1
  have h₁ (v : ({0}ᶜ : Set (Ambient n))) :
      R ((homeomorphUnitSphereProd _ v).2) * F ((homeomorphUnitSphereProd _ v).1 : Ambient n) =
      B.indicator (fun z ↦ F (‖z‖⁻¹ • z)) v.val := by
    by_cases hv : ‖v.val‖ < 1 <;> simp [B, R, indicator, Metric.mem_ball, dist_zero_right, hv]
  have h₂ (v : ({0}ᶜ : Set (Ambient n))) :
      R ((homeomorphUnitSphereProd _ v).2) = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) v.val := by
    by_cases hv : ‖v.val‖ < 1 <;> simp [B, R, indicator, Metric.mem_ball, dist_zero_right, hv]
  dsimp only at h
  simp_rw [h₁, h₂] at h
  rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton,
    lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton,
    lintegral_indicator Metric.isOpen_ball.measurableSet, lintegral_indicator Metric.isOpen_ball.measurableSet] at h
  simpa [B] using h

/-- Split the uniform sphere in an orthogonal frame into its first coordinate
and its normalized transverse vector. -/
theorem sphere_axial_direction (m : ℕ) (hm : 0 < m)
    (e : Ambient (m+1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Ambient m))
    (A : ℝ → ℝ≥0∞) (hA : Measurable A) (F : Ambient m → ℝ≥0∞) (hF : Measurable F) :
    let dir := fun w : Ambient m ↦ ‖w‖⁻¹ • w
    (∫⁻ x : Sphere (m+1), A (e x).fst * F (dir (e x).snd) ∂uniform (m+1)) =
      (∫⁻ x : Sphere (m+1), A (e x).fst ∂uniform (m+1)) *
        ∫⁻ v : Sphere m, F v ∂uniform m := by
  intro dir
  let B := Metric.ball (0 : Ambient (m+1)) 1
  let M := volume B
  have hM : M ≠ 0 := Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr one_pos)
  have hMf : M ≠ ⊤ := measure_ball_lt_top.ne
  let W := fun u r : ℝ ↦ if u^2 + r^2 < 1 then A (u / Real.sqrt (u^2 + r^2)) else 0
  have splitTest (G : Ambient m → ℝ≥0∞) (hG : Measurable G) :
      M * (∫⁻ x : Sphere (m+1), A (e x).fst * G (dir (e x).snd) ∂uniform (m+1)) =
        ∫⁻ u : ℝ, ∫⁻ w : Ambient m, W u ‖w‖ * G (dir w) := by
    let H := fun x : Ambient (m+1) ↦ A (e x).fst * G (dir (e x).snd)
    have hH : Measurable H := by dsimp [H, dir]; fun_prop
    have h := ball_normalized_integral (m+1) (by omega) H hH
    rw [← h, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
    have hf := e.symm.measurePreserving.comp (WithLp.volume_preserving_toLp ℝ (Ambient m))
    have hh := hf.lintegral_comp (f := B.indicator fun x ↦ H (‖x‖⁻¹ • x))
      ((hH.comp (by fun_prop)).indicator Metric.isOpen_ball.measurableSet)
    rw [← hh, ← lintegral_prod (fun z : ℝ × Ambient m ↦ W z.1 ‖z.2‖ * G (dir z.2))]
    · apply lintegral_congr
      rintro ⟨u,w⟩
      let z := WithLp.toLp 2 (u,w)
      have hs : ‖z‖ ^ 2 = u^2 + ‖w‖^2 := by simpa [z] using WithLp.prod_norm_sq_eq_of_L2 z
      have hr : Real.sqrt (u^2 + ‖w‖^2) = ‖z‖ := by rw [← hs, Real.sqrt_sq (norm_nonneg _)]
      have hb : e.symm z ∈ B ↔ u^2 + ‖w‖^2 < 1 := by
        simp only [B, Metric.mem_ball, dist_zero_right, e.symm.norm_map, ← hs]
        constructor <;> intro hh <;> nlinarith [norm_nonneg z]
      change B.indicator _ (e.symm z) = _
      by_cases hin : u^2 + ‖w‖^2 < 1
      · rw [indicator_of_mem (hb.mpr hin)]
        simp only [H, e.map_smul, e.apply_symm_apply, e.symm.norm_map, W, ite_eq_left hin, hr]
        change A (‖z‖⁻¹ * u) * G (dir (‖z‖⁻¹ • w)) = _
        rw [div_eq_inv_mul]
        by_cases hz : ‖z‖ = 0
        · have hw : w = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg u, norm_nonneg w])
          simp [hw, dir]
        · simp [dir, norm_smul, smul_smul, hz]
      · simp [indicator_of_notMem (fun h ↦ hin (hb.mp h)), W, hin]
    · apply Measurable.aemeasurable
      apply Measurable.mul
      · exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
          (hA.comp (by fun_prop)) measurable_const
      · dsimp [dir]; fun_prop
  have full := ball_axial_direction m hm A hA (fun v ↦ F v) (hF.comp measurable_subtype_coe)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  dsimp only at full
  simp only [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe] at full
  have pull (K : Ambient m → ℝ≥0∞) :
      (∫⁻ w : ({0}ᶜ : Set (Ambient m)), K w ∂volume.comap Subtype.val) = ∫⁻ w, K w := by
    rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  change (∫⁻ u : ℝ, ∫⁻ w : ({0}ᶜ : Set (Ambient m)), W u ‖w.val‖ * F (dir w.val)
    ∂volume.comap Subtype.val) = _ at full
  change _ = (∫⁻ u : ℝ, ∫⁻ w : ({0}ᶜ : Set (Ambient m)), W u ‖w.val‖
    ∂volume.comap Subtype.val) * _ at full
  have hf₁ (u : ℝ) := pull (fun w ↦ W u ‖w‖ * F (dir w))
  have hf₂ (u : ℝ) := pull (fun w ↦ W u ‖w‖)
  simp_rw [hf₁, hf₂] at full
  have one := splitTest (fun _ ↦ 1) measurable_const
  simp only [mul_one] at one
  apply (ENNReal.mul_right_inj hM hMf).mp
  rw [← mul_assoc, splitTest F hF, one]
  exact full

#print axioms ball_normalized_integral
#print axioms sphere_axial_direction

/-- Action of an ambient orthogonal transformation on the unit sphere. -/
def rotate {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n) (x : Sphere n) : Sphere n :=
  ⟨e x, mem_sphere_zero_iff_norm.mpr (by simp [mem_sphere_zero_iff_norm.mp x.property])⟩

open scoped Pointwise in
theorem uniform_rotate {n : ℕ} (e : Ambient n ≃ₗᵢ[ℝ] Ambient n) :
    MeasurePreserving (rotate e) (uniform n) (uniform n) := by
  have hm : Measurable (rotate e) :=
    (e.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable
  refine ⟨hm, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hm hs, uniform, Measure.smul_apply, Measure.smul_apply,
    Measure.toSphere_apply' _ (hm hs), Measure.toSphere_apply' _ hs]
  congr 2
  let C := fun s : Set (Sphere n) ↦ Ioo (0 : ℝ) 1 • (Subtype.val '' s)
  have he : C (rotate e ⁻¹' s) = e ⁻¹' C s := by
    ext z
    constructor
    · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨r, hr, _, ⟨rotate e w, hw, rfl⟩, (e.map_smul r w).symm⟩
    · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, hz⟩
      refine ⟨r, hr, _, ⟨rotate e.symm w, ?_, rfl⟩, e.injective ?_⟩
      · simpa [rotate, Set.mem_preimage] using hw
      · simpa [rotate] using hz
  change volume (C _) = volume (C s)
  rw [he]
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

/-- For two independent sphere draws the full Gram test has the same integral at any pole. -/
theorem fixedPole_gram_integral {n : ℕ} (x p : Sphere n)
    (F : ℝ × ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let test := fun (u : Sphere n) (z : Sphere n × Sphere n) ↦
      F (inner ℝ (u : Ambient n) z.1, inner ℝ (u : Ambient n) z.2,
        inner ℝ (z.1 : Ambient n) z.2)
    ∫⁻ z, test x z ∂(uniform n).prod (uniform n) =
      ∫⁻ z, test p z ∂(uniform n).prod (uniform n) := by
  intro test
  have : 0 < n := by
    by_contra! h
    obtain rfl : n = 0 := by omega
    have hz : (x : Ambient 0) = 0 := Subsingleton.elim _ _
    simpa only [hz, norm_zero, zero_ne_one] using mem_sphere_zero_iff_norm.mp x.property
  let := uniform_probability this
  let e := (ℝ ∙ ((x : Ambient n) - p))ᗮ.reflection
  have he : e x = p := Submodule.reflection_sub
    ((mem_sphere_zero_iff_norm.mp x.property).trans (mem_sphere_zero_iff_norm.mp p.property).symm)
  have h := ((uniform_rotate e).prod (uniform_rotate e)).lintegral_comp (f := test p)
    (by dsimp [test]; fun_prop)
  rw [← h]
  apply lintegral_congr
  intro z
  simp only [test, Prod.map, rotate, ← he, e.inner_map_map]

#print axioms uniform_rotate
#print axioms fixedPole_gram_integral

private def splitCoord {m : ℕ} (e : Ambient (m+1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Ambient m))
    (x : Sphere (m+1)) : ℝ × Ambient m := ((e x).fst, ‖(e x).snd‖⁻¹ • (e x).snd)

private theorem splitCoord_law (m : ℕ) (hm : 0 < m)
    (e : Ambient (m+1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Ambient m)) :
    let μ := uniform (m+1)
    let a := fun x : Sphere (m+1) ↦ (e x).fst
    μ.map (splitCoord e) = (μ.map a).prod ((uniform m).map Subtype.val) := by
  intro μ a
  let := uniform_probability hm
  let := uniform_probability (n := m+1) (by omega)
  have : IsProbabilityMeasure μ := uniform_probability (by omega)
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hc : Measurable (splitCoord e) := by unfold splitCoord; fun_prop
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.prod_prod, Measure.map_apply ha hs, Measure.map_apply measurable_subtype_coe ht,
    Measure.map_apply hc (hs.prod ht), ← lintegral_indicator_one (hc (hs.prod ht)),
    ← lintegral_indicator_one (ha hs), ← lintegral_indicator_one (measurable_subtype_coe ht)]
  convert sphere_axial_direction m hm e (s.indicator (fun _ ↦ 1)) (measurable_const.indicator hs)
    (t.indicator (fun _ ↦ 1)) (measurable_const.indicator ht) using 1
  · apply lintegral_congr
    intro x
    have heq : x ∈ splitCoord e ⁻¹' (s ×ˢ t) ↔
        (e x).fst ∈ s ∧ ‖(e x).snd‖⁻¹ • (e x).snd ∈ t := Iff.rfl
    by_cases h : (e x).fst ∈ s
    · by_cases k : ‖(e x).snd‖⁻¹ • (e x).snd ∈ t
      · simp [indicator, heq.mpr ⟨h,k⟩, h, k]
      · have hn := mt heq.mp (fun hk ↦ k hk.2)
        simp [indicator, hn, h, k]
    · have hn := mt heq.mp (fun hk ↦ h hk.1)
      simp [indicator, hn, h]
  · rfl

private theorem splitCoord_inner {m : ℕ} (e : Ambient (m+1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Ambient m))
    (x y : Sphere (m+1)) :
    inner ℝ (x : Ambient (m+1)) y = angularThird (splitCoord e x).1 (splitCoord e y).1
      (inner ℝ (splitCoord e x).2 (splitCoord e y).2) := by
  have normSq (z : Sphere (m+1)) : 1 - (e z).fst ^ 2 = ‖(e z).snd‖ ^ 2 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 (e z)
    rw [e.norm_map, mem_sphere_zero_iff_norm.mp z.property] at h
    simpa [Real.norm_eq_abs, sq_abs] using (by linarith : 1 - ‖(e z).fst‖^2 = ‖(e z).snd‖^2)
  simp only [splitCoord, angularThird, normSq, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), real_inner_smul_left, real_inner_smul_right]
  rw [← e.inner_map_map, WithLp.prod_inner_apply]
  change inner ℝ (e x).fst (e y).fst + inner ℝ (e x).snd (e y).snd = _
  rw [Real.inner_apply]
  by_cases hx : (e x).snd = 0
  · simp [hx, mul_comm]
  by_cases hy : (e y).snd = 0
  · simp [hy, mul_comm]
  field_simp [norm_ne_zero_iff.mpr hx, norm_ne_zero_iff.mpr hy]

private theorem splitCoord_test {m : ℕ} (hm : 0 < m)
    (e : Ambient (m+1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Ambient m))
    (G : ℝ × Ambient m → ℝ≥0∞) (hG : Measurable G) :
    let a := fun x : Sphere (m+1) ↦ (e x).fst
    (∫⁻ x, G (splitCoord e x) ∂uniform (m+1)) =
      ∫⁻ b, ∫⁻ v : Sphere m, G (b,v.val) ∂uniform m ∂(uniform (m+1)).map a := by
  intro a
  let := uniform_probability hm
  have hc : Measurable (splitCoord e) := by unfold splitCoord; fun_prop
  rw [← lintegral_map hG hc, splitCoord_law m hm e, lintegral_prod _ hG.aemeasurable]
  apply lintegral_congr
  intro b
  exact lintegral_map (hG.comp (measurable_const.prodMk measurable_id)) measurable_subtype_coe

set_option maxHeartbeats 1800000 in
/-- Three independent sphere draws have the successive axial and transverse cosine laws. -/
theorem angularDisintegration {n : ℕ} (hn : 3 ≤ n) : AngularDisintegration n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
  -- The orthogonal complement of the pole has ambient dimension m+1.
  let d := m+1
  change AngularDisintegration (d+1)
  have hm : 1 ≤ m := by omega
  let E := WithLp 2 (ℝ × Ambient d)
  have hd : Module.finrank ℝ E = d+1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × Ambient d)).finrank_eq, Module.finrank_prod]
    simp [Nat.add_comm]
  let e := ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr.symm
  let axis : E := WithLp.toLp 2 (1,0)
  let pole : Sphere (d+1) := ⟨e.symm axis, mem_sphere_zero_iff_norm.mpr (by
    rw [e.symm.norm_map, WithLp.norm_toLp_fst]; norm_num)⟩
  have axial (x : Sphere (d+1)) : inner ℝ (pole : Ambient (d+1)) x = (e x).fst := by
    change inner ℝ (e.symm axis) x = _
    rw [← e.inner_map_map, e.apply_symm_apply, WithLp.prod_inner_apply]
    simp [axis]
  let μ := uniform (d+1)
  let σ := uniform d
  let a := fun x : Sphere (d+1) ↦ (e x).fst
  let ρ := μ.map a
  let p := (((d+1 : ℕ) : ℝ)-4)/2
  have law : ρ = volume.withDensity (weight (p+1/2)) := by
    have h := pole_law_of_pos d (by omega) pole
    simp_rw [axial] at h
    convert h using 3
    dsimp [p]
    push_cast
    ring
  have tlaw (v : Sphere d) := pole_law_of_pos m hm v
  let : IsProbabilityMeasure μ := uniform_probability (by omega)
  let : IsProbabilityMeasure σ := uniform_probability (by omega)

  intro F hF
  let T := fun (z w : ℝ × Ambient d) ↦
    F (z.1, w.1, angularThird z.1 w.1 (inner ℝ z.2 w.2))
  have hT : Measurable (Function.uncurry T) := by dsimp [T, angularThird, Function.uncurry]; fun_prop
  let K := fun z : ℝ × Ambient d ↦ ∫⁻ y, T z (splitCoord e y) ∂μ
  have hK : Measurable K := by
    apply Measurable.lintegral_prod_right' (f := fun z ↦ T z.1 (splitCoord e z.2))
    exact hT.comp (measurable_fst.prodMk ((show Measurable (splitCoord e) by
      unfold splitCoord; fun_prop).comp measurable_snd))
  let test := fun (u : Sphere (d+1)) (z : Sphere (d+1) × Sphere (d+1)) ↦
    F (inner ℝ (u : Ambient (d+1)) z.1, inner ℝ (u : Ambient (d+1)) z.2,
      inner ℝ (z.1 : Ambient (d+1)) z.2)
  change (∫⁻ z, test z.1 z.2 ∂μ.prod (μ.prod μ)) = _
  rw [lintegral_prod _ (by dsimp [test]; fun_prop : Measurable _).aemeasurable]
  have fixed (u : Sphere (d+1)) := fixedPole_gram_integral u pole F hF
  change ∀ u, (∫⁻ z, test u z ∂μ.prod μ) = ∫⁻ z, test pole z ∂μ.prod μ at fixed
  simp_rw [fixed]
  rw [lintegral_const, measure_univ, mul_one,
    lintegral_prod _ (by dsimp [test]; fun_prop : Measurable _).aemeasurable]
  simp only [test, axial]
  simp only [splitCoord_inner e]
  change (∫⁻ x, K (splitCoord e x) ∂μ) = _
  rw [splitCoord_test (by omega) e K hK]
  let J := fun a b t : ℝ ↦ F (a,b,angularThird a b t)
  have hw (q : ℝ) : Measurable (weight q) := by
    unfold weight; exact Measurable.ite measurableSet_Ioo (by fun_prop) measurable_const
  have transLaw (b c : ℝ) (v : Sphere d) :
      (∫⁻ w : Sphere d, T (b,v.val) (c,w.val) ∂σ) =
        ∫⁻ t, weight p t * J b c t := by
    have hJ : Measurable (J b c) := by dsimp [J, angularThird]; fun_prop
    have h := tlaw v
    have expEq : ((m:ℝ)+1-3)/2 = p := by dsimp [p,d]; push_cast; ring
    rw [expEq] at h
    change (∫⁻ w : Sphere d, J b c (inner ℝ (v : Ambient d) w) ∂uniform d) = _
    have hf : Measurable (fun w : Sphere d ↦ inner ℝ (v : Ambient d) (w : Ambient d)) := by fun_prop
    rw [← lintegral_map hJ hf, h, lintegral_withDensity_eq_lintegral_mul _ (hw _) hJ]
    rfl
  have hKv (b : ℝ) (v : Sphere d) :
      K (b,v.val) = ∫⁻ c, ∫⁻ t, weight p t * J b c t ∂volume ∂ρ := by
    dsimp only [K]
    rw [splitCoord_test (by omega) e (T (b,v.val)) (hT.comp (measurable_const.prodMk measurable_id))]
    apply lintegral_congr
    intro c
    exact transLaw b c v
  simp_rw [hKv, lintegral_const]
  change (∫⁻ b, (∫⁻ c, ∫⁻ t, weight p t * J b c t ∂volume ∂ρ) * σ univ ∂ρ) = _
  simp only [measure_univ, mul_one, law]
  rw [lintegral_withDensity_eq_lintegral_mul _ (hw _) (by dsimp [J, angularThird]; fun_prop)]
  apply lintegral_congr
  intro b
  simp only [Pi.mul_apply]
  rw [lintegral_withDensity_eq_lintegral_mul _ (hw _) (by dsimp [J, angularThird]; fun_prop),
    ← lintegral_const_mul]
  · apply lintegral_congr
    intro c
    exact (mul_assoc _ _ _).symm
  · dsimp [J, angularThird]; fun_prop

theorem tripleLaw_of_angularDisintegration {n : ℕ} (hn : 3 ≤ n)
    (h : AngularDisintegration n) : TripleLaw n := by
  apply Measure.ext
  intro s hs
  let F := s.indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hs
  let g := fun z : Sphere n × Sphere n × Sphere n ↦
    (inner ℝ (z.1 : Ambient n) (z.2.1 : Ambient n),
     inner ℝ (z.1 : Ambient n) (z.2.2 : Ambient n),
     inner ℝ (z.2.1 : Ambient n) (z.2.2 : Ambient n))
  have hg : Measurable g := by dsimp [g]; fun_prop
  change Measure.map g _ s = _
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs (μ := volume.withDensity (tripleWeight n))]
  change (∫⁻ z, F z ∂Measure.map g _) = ∫⁻ z, F z ∂_
  rw [lintegral_map hF hg]
  change (∫⁻ z, F (g z) ∂_) = ∫⁻ z, F z ∂_
  rw [h F hF, lintegral_withDensity_eq_lintegral_mul _ (measurable_tripleWeight n) hF,
    Measure.volume_eq_prod, lintegral_prod _ ((measurable_tripleWeight n).mul hF).aemeasurable]
  apply lintegral_congr
  intro a
  have hm : Measurable (fun y : ℝ × ℝ ↦ (tripleWeight n * F) (a,y)) :=
    ((measurable_tripleWeight n).mul hF).comp (measurable_const.prodMk measurable_id)
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro b
  exact (triple_fiber_test n hn a b (fun c ↦ F (a,b,c)) (by fun_prop)).symm

theorem triple_law {n : ℕ} (hn : 3 ≤ n) : TripleLaw n :=
  tripleLaw_of_angularDisintegration hn (angularDisintegration hn)

#print axioms angularDisintegration
#print axioms triple_law

abbrev OffDiagonal (s : ℕ) := {ij : Fin s × Fin s // ij.1 < ij.2}

/-- All pole cosines and off-diagonal Gram entries of a finite sample in a split frame. -/
theorem tuple_angular_integral {m s : ℕ} (hm : 0 < m)
    (e : Ambient (m+1) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Ambient m))
    (F : (Fin s → ℝ) × (OffDiagonal s → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    let ρ := (uniform (m+1)).map (fun x : Sphere (m+1) ↦ (e x).fst)
    (∫⁻ z : Fin s → Sphere (m+1), F (fun i ↦ (e (z i)).fst,
      fun ij ↦ inner ℝ (z ij.val.1 : Ambient (m+1)) (z ij.val.2))
      ∂Measure.pi (fun _ ↦ uniform (m+1))) =
    ∫⁻ w : Fin s → ℝ × Ambient m, F (fun i ↦ (w i).1,
      fun ij ↦ angularThird (w ij.val.1).1 (w ij.val.2).1
        (inner ℝ (w ij.val.1).2 (w ij.val.2).2))
      ∂Measure.pi (fun _ ↦ ρ.prod ((uniform m).map Subtype.val)) := by
  intro ρ
  let := uniform_probability hm
  let := uniform_probability (n := m+1) (by omega)
  let : IsFiniteMeasure ρ := by dsimp [ρ]; infer_instance
  have hc : Measurable (splitCoord e) := by unfold splitCoord; fun_prop
  have hp : MeasurePreserving (splitCoord e) (uniform (m+1))
      (ρ.prod ((uniform m).map Subtype.val)) := ⟨hc, splitCoord_law m hm e⟩
  have h := measurePreserving_pi (fun _ : Fin s ↦ uniform (m+1))
    (fun _ ↦ ρ.prod ((uniform m).map Subtype.val)) (fun _ ↦ hp)
  let K := fun w : Fin s → ℝ × Ambient m ↦ F (fun i ↦ (w i).1,
    fun ij ↦ angularThird (w ij.val.1).1 (w ij.val.2).1
      (inner ℝ (w ij.val.1).2 (w ij.val.2).2))
  have hK : Measurable K := by dsimp [K, angularThird]; fun_prop
  change _ = ∫⁻ w, K w ∂_
  rw [← h.lintegral_comp hK]
  apply lintegral_congr
  intro z
  simp only [K, splitCoord_inner e]
  rfl

/-- The random first direction can be integrated out for a Gram test of any order. -/
theorem randomPole_gram_integral {n s : ℕ} (hn : 0 < n) (p : Sphere n)
    (F : (Fin s → ℝ) × (OffDiagonal s → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    let test := fun (u : Sphere n) (z : Fin s → Sphere n) ↦
      F (fun i ↦ inner ℝ (u : Ambient n) (z i),
        fun ij ↦ inner ℝ (z ij.val.1 : Ambient n) (z ij.val.2))
    (∫⁻ y, test y.1 y.2 ∂(uniform n).prod (Measure.pi fun _ ↦ uniform n)) =
      ∫⁻ z, test p z ∂Measure.pi (fun _ ↦ uniform n) := by
  intro test
  let := uniform_probability hn
  rw [lintegral_prod _ (by dsimp [test]; fun_prop : Measurable _).aemeasurable]
  have fixed (u : Sphere n) : (∫⁻ z, test u z ∂Measure.pi (fun _ ↦ uniform n)) =
      ∫⁻ z, test p z ∂Measure.pi (fun _ ↦ uniform n) := by
    let e := (ℝ ∙ ((u : Ambient n) - p))ᗮ.reflection
    have he : e u = p := Submodule.reflection_sub
      ((mem_sphere_zero_iff_norm.mp u.property).trans
        (mem_sphere_zero_iff_norm.mp p.property).symm)
    have hp := measurePreserving_pi (fun _ : Fin s ↦ uniform n) (fun _ ↦ uniform n)
      (fun _ ↦ uniform_rotate e)
    rw [← hp.lintegral_comp (f := test p) (by dsimp [test]; fun_prop)]
    apply lintegral_congr
    intro z
    simp only [test, rotate, ← he, e.inner_map_map]
  simp_rw [fixed]
  simp

#print axioms randomPole_gram_integral

/-- Recursive sampling law for all pairwise inner products, including the random pole. -/
theorem gram_angular_recursion {m s : ℕ} (hm : 0 < m)
    (F : (Fin s → ℝ) × (OffDiagonal s → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y : Sphere (m+1) × (Fin s → Sphere (m+1)),
      F (fun i ↦ inner ℝ (y.1 : Ambient (m+1)) (y.2 i),
        fun ij ↦ inner ℝ (y.2 ij.val.1 : Ambient (m+1)) (y.2 ij.val.2))
      ∂(uniform (m+1)).prod (Measure.pi fun _ ↦ uniform (m+1))) =
    ∫⁻ w : Fin s → ℝ × Ambient m, F (fun i ↦ (w i).1,
      fun ij ↦ angularThird (w ij.val.1).1 (w ij.val.2).1
        (inner ℝ (w ij.val.1).2 (w ij.val.2).2))
      ∂Measure.pi (fun _ ↦ (volume.withDensity (weight (((m:ℝ)+1-3)/2))).prod
        ((uniform m).map Subtype.val)) := by
  let E := WithLp 2 (ℝ × Ambient m)
  have hd : Module.finrank ℝ E = m+1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × Ambient m)).finrank_eq, Module.finrank_prod]
    simp [Nat.add_comm]
  let e := ((stdOrthonormalBasis ℝ E).reindex (finCongr hd)).repr.symm
  let axis : E := WithLp.toLp 2 (1,0)
  let p : Sphere (m+1) := ⟨e.symm axis, mem_sphere_zero_iff_norm.mpr (by
    rw [e.symm.norm_map, WithLp.norm_toLp_fst]; norm_num)⟩
  have axial (x : Sphere (m+1)) : inner ℝ (p : Ambient (m+1)) x = (e x).fst := by
    change inner ℝ (e.symm axis) x = _
    rw [← e.inner_map_map, e.apply_symm_apply, WithLp.prod_inner_apply]
    simp [axis]
  have hρ := pole_law_of_pos m hm p
  simp_rw [axial] at hρ
  calc
    _ = _ := randomPole_gram_integral (by omega) p F hF
    _ = _ := by
      simp only [axial]
      simpa only [hρ] using tuple_angular_integral hm e F hF

#print axioms gram_angular_recursion

/-- Schur determinant for adjoining a pole with axial row B and transverse scales r. -/
theorem angular_block_det {s : ℕ} (B : Matrix Unit (Fin s) ℝ)
    (r : Fin s → ℝ) (H : Matrix (Fin s) (Fin s) ℝ) :
    (Matrix.fromBlocks 1 B B.transpose
      (B.transpose * B + Matrix.diagonal r * H * Matrix.diagonal r)).det =
      (∏ i, r i)^2 * H.det := by
  rw [Matrix.det_fromBlocks_one₁₁, add_sub_cancel_left]
  simp only [Matrix.det_mul, Matrix.det_diagonal]
  ring

#print axioms tuple_angular_integral
#print axioms angular_block_det

/-- Jacobian of the affine change from transverse to ambient off-diagonal entries. -/
theorem angular_fiber_volume {s : ℕ} (a r : Fin s → ℝ) (hr : ∀ i, 0 < r i) :
    Measure.map (fun x : OffDiagonal s → ℝ ↦ fun ij ↦
      a ij.val.1 * a ij.val.2 + (r ij.val.1 * r ij.val.2) * x ij) volume =
      ENNReal.ofReal (∏ ij : OffDiagonal s, r ij.val.1 * r ij.val.2)⁻¹ • volume := by
  classical
  let d := fun ij : OffDiagonal s ↦ r ij.val.1 * r ij.val.2
  let b := fun ij : OffDiagonal s ↦ a ij.val.1 * a ij.val.2
  let L := (Matrix.diagonal d).toLin'
  have hd : 0 < ∏ ij, d ij := Finset.prod_pos fun ij _ ↦ mul_pos (hr _) (hr _)
  have he : (fun x : OffDiagonal s → ℝ ↦ fun ij ↦
      a ij.val.1 * a ij.val.2 + (r ij.val.1 * r ij.val.2) * x ij) = (b + ·) ∘ L := by
    funext x ij
    simp [L, b, d, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rw [he, ← Measure.map_map (measurable_const_add _) L.continuous_of_finiteDimensional.measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (by simpa using hd.ne'),
    Matrix.det_diagonal, abs_of_pos (inv_pos.mpr hd), Measure.map_smul, map_add_left_eq_self]
  exact (measurable_const_add b).aemeasurable

#print axioms angular_fiber_volume

def correlation {s : ℕ} (x : OffDiagonal s → ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  fun i j ↦ if h : i < j then x ⟨(i,j),h⟩ else if h : j < i then x ⟨(j,i),h⟩ else 1

/-- Product of scalar projection normalizers for the successive orthogonal complements.
The exponent s(s-1)/4 on π is the sum of the exponents j/2 below. -/
def gramConstant (n s : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (s-1), Real.Gamma ((n:ℝ)/2) /
    (Real.pi ^ (((j:ℝ)+1)/2) * Real.Gamma (((n:ℝ)-(j+1))/2))

/-- Normalizer recursion for peeling one pole and passing to its orthogonal complement. -/
theorem gramConstant_recursion (m k : ℕ) (hm : 0 < m) :
    gramConstant (m+1) (k+2) =
      normalizer (((m:ℝ)+1-3)/2)^(k+1) * gramConstant m (k+1) := by
  let c := normalizer (((m:ℝ)+1-3)/2)
  have hpos : 0 < (m:ℝ) := by exact_mod_cast hm
  have hc : c = Real.Gamma (((m:ℝ)+1)/2) / (Real.pi^(1/2:ℝ) * Real.Gamma ((m:ℝ)/2)) := by
    dsimp [c]
    rw [normalizer_gamma (by linarith), ← Real.sqrt_eq_rpow]
    congr 2 <;> congr 1 <;> ring
  let f := fun (n j : ℕ) ↦ Real.Gamma ((n:ℝ)/2) /
    (Real.pi ^ (((j:ℝ)+1)/2) * Real.Gamma (((n:ℝ)-(j+1))/2))
  have h0 : f (m+1) 0 = c := by simp [f, hc]
  have hs (j : ℕ) : f (m+1) (j+1) = c * f m j := by
    dsimp [f]
    push_cast
    rw [hc, show ((j:ℝ)+1+1)/2 = 1/2 + (j+1)/2 by ring,
      Real.rpow_add Real.pi_pos, show (m:ℝ)+1-(j+1+1) = m-(j+1) by ring]
    have hn := (Real.Gamma_pos_of_pos (half_pos hpos)).ne'
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp [hn]
  change (∏ j ∈ Finset.range (k+1), f (m+1) j) =
    c^(k+1) * ∏ j ∈ Finset.range k, f m j
  rw [Finset.prod_range_succ', h0]
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  simp [pow_succ, mul_assoc, mul_comm]

#print axioms gramConstant_recursion

open Classical in
def SphericalGramFormula (n s : ℕ) : Prop :=
  Measure.map (fun z : Fin s → Sphere n ↦ fun ij : OffDiagonal s ↦
    inner ℝ (z ij.val.1 : Ambient n) (z ij.val.2 : Ambient n))
    (Measure.pi fun _ ↦ uniform n) = volume.withDensity (fun x ↦
      if (correlation x).PosDef then
        ENNReal.ofReal (gramConstant n s * (correlation x).det ^ (((n:ℝ)-s-1)/2)) else 0)

#print axioms capSection_volume
#print axioms capRadius_integral
#print axioms axialCap_volume
#print axioms cone_positive_volume
#print axioms capSlice_tail
#print axioms capSlice_normalized

#print axioms normalizer_gamma
#print axioms transverse_ball_volume
#print axioms normalized_positive_cap
#print axioms pole_law
#print axioms pair_law
#print axioms pole_law_of_pos
#print axioms ball_axial_direction
#print axioms transverse_slice_integral
#print axioms transverse_slice_cosine
#print axioms axial_pair_law
#print axioms transverse_inner

end SigabaNeo.Rogers.Gram
