import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3FrameShear
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder3FrameCount

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace SigabaNeo.Rogers.Frame

private lemma tsum_prod {V : Type*} (k : ℕ) (u : Fin k → V → ℝ≥0∞) :
    (∑' z : Fin k → V, ∏ i, u i (z i)) = ∏ i, ∑' v, u i v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ, ← ih, ← ENNReal.tsum_mul_right]
    rw [← (Fin.consEquiv (fun _ : Fin (k+1) ↦ V)).tsum_eq (fun z ↦ ∏ i, u i (z i))]
    simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [_root_.tsum_prod (f := fun (v : V) (z : Fin k → V) ↦ u 0 v * ∏ i, u i.succ (z i))]
    exact tsum_congr fun v ↦ (ENNReal.tsum_mul_left ..)

private lemma exists_box {n} (hn : 3 < n) :
    ∃ (c : FrameSpace n 3) (r : ℝ), 0 < r ∧
      (∀ x : FrameSpace n 3, (∀ a, x a ∈ ball (c a) r) → LinearIndependent ℝ x) ∧
      (∀ a, 0 ∉ ball (c a) r) ∧ (∀ a, ball (c a) r ⊆ ball 0 1) := by
  let e : Fin 3 ↪ Fin n := Fin.castLEEmb (by omega)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let c (a : Fin 3) := (2⁻¹ : ℝ) • b (e a)
  have hc : LinearIndependent ℝ c :=
    (b.toBasis.linearIndependent.comp e e.injective).units_smul
      (fun _ ↦ Units.mk0 (2⁻¹ : ℝ) (by norm_num))
  obtain ⟨ε,hε,he⟩ := Metric.isOpen_iff.mp isOpen_setOfPred_linearIndependent c hc
  refine ⟨c,min ε (1/4), lt_min hε (by norm_num), ?_, ?_, ?_⟩
  · intro x hx
    apply he
    rw [ball_pi c hε]
    exact fun a _ ↦ ball_subset_ball (min_le_left ..) (hx a)
  all_goals have hnrm (a : Fin 3) : ‖c a‖ = 2⁻¹ := by norm_num [c, norm_smul, b.norm_eq_one]
  · intro a ha
    rw [mem_ball, dist_zero_left, hnrm] at ha
    have := min_le_right ε (1/4 : ℝ)
    linarith
  · intro a x hx
    rw [mem_ball] at *
    have := dist_triangle x (c a) 0
    rw [dist_zero_right, dist_zero_right, hnrm] at this
    rw [dist_zero_right]
    have := min_le_right ε (1/4 : ℝ)
    linarith

theorem rogers_three_frame_measure (n : ℕ) (hn : 3 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤) :
    frameMeasure (k := 3) D = groupHaar n D • Measure.pi (fun _ ↦ volume) := by
  classical
  obtain ⟨C,hC⟩ := tripleFrame_proportional hn hd hf
  obtain ⟨c,r,hr,indep,avoid,inside⟩ := exists_box hn
  let V := ENNReal.ofReal (r^n)
  have V0 : V ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have Vf : V ≠ ⊤ := ENNReal.ofReal_ne_top
  let F (j : ℕ) (x : FrameSpace n 3) := ∏ i, offTest (c i) r j (x i)
  have meas (j : ℕ) : Measurable (F j) := Finset.measurable_prod _ fun i _ ↦
    (measurable_const.indicator isOpen_ball.measurableSet).comp (measurable_pi_apply i)
  let W (j : ℕ) (g : SL n) := tupleWorkload (F j) (QuotientGroup.mk g)
  have factor (j) (g : SL n) : W j g = ∏ i, offWork (c i) r j g := by
    rw [show W j g = _ from tsum_prod 3 (fun i (v : {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}) ↦ offTest (c i) r j v.val)]
    exact Finset.prod_congr rfl fun i _ ↦ ((Equiv.funUnique (Fin 1)
      {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}).tsum_eq _).symm
  have point (g : SL n) : Tendsto (fun j ↦ W j g) atTop (𝓝 (V^3)) := by
    have lim (i) := offWork_limit n (by omega) g (c i) r (avoid i)
    have hv0 : volume (ball (0 : E n) 1) ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
    simp only [volume.addHaar_ball_of_pos (c _) hr, finrank_euclideanSpace_fin,
      ENNReal.mul_div_cancel_right hv0 measure_ball_lt_top.ne] at lim
    simp only [factor, Fin.prod_univ_three]
    simpa [pow_succ, V] using ENNReal.Tendsto.mul
      (ENNReal.Tendsto.mul (lim 0) (Or.inr Vf) (lim 1) (Or.inr Vf)) (Or.inr Vf) (lim 2)
      (Or.inr (ENNReal.mul_ne_top Vf Vf))
  have bound (j : ℕ) (g : SL n) : W j g ≤ (densityWork n j g)^3 := by
    rw [factor, show (densityWork n j g)^3 = ∏ _ : Fin 3, densityWork n j g by simp]
    apply Finset.prod_le_prod
    intro i _
    apply tsum_le_tsum
    intro v
    change offTest _ _ _ _ ≤ densityTest _ _ _
    unfold offTest densityTest
    refine Set.indicator_le_indicator_of_subset ?_ (fun _ ↦ zero_le) _
    intro x hx
    have hp : 0 < (j : ℝ)+1 := by positivity
    have hh := inside i ((off_mem _ _ _ hp).mp hx)
    have hh' := (off_mem (0 : E n) x 1 hp).mpr hh
    simpa [densityBall] using hh'
  have domain (j : ℕ) : (∫⁻ g in D, W j g ∂groupHaar n) = ∫⁻ x, F j x ∂frameMeasure D := by
    rw [frameMeasure_lintegral D _ (meas j), show (∫⁻ g in D, W j g ∂groupHaar n) = _ from
      domain_lintegral_tupleWorkload _ D (meas j)]
    symm
    apply tsum_subtype_eq_of_support_subset (s := independent n 3) (f := fun z ↦
      ∫⁻ g in D, F j (fun i ↦ WithLp.toLp 2 (g • fun a ↦ ((z i).val a : ℝ))) ∂groupHaar n)
    intro z hz
    by_contra h
    apply hz
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with g
    by_contra hx
    have hall (i) : offTest (c i) r j (WithLp.toLp 2 (g • fun a ↦ ((z i).val a : ℝ))) ≠ 0 :=
      fun he ↦ hx (Finset.prod_eq_zero (Finset.mem_univ i) he)
    have hp : 0 < (j : ℝ)+1 := by positivity
    let y (i : Fin 3) : E n := WithLp.toLp 2 (g • fun a ↦ ((z i).val a : ℝ))
    have hy := indep (fun i ↦ ((j : ℝ)+1)⁻¹ • y i) fun i ↦ (off_mem _ _ _ hp).mp
      (by by_contra hm; exact hall i (Set.indicator_of_notMem hm _))
    let e := g.toLin'.trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
    apply h
    apply (linearIndependent_algebraMap_comp_iff (S := ℝ) (v := fun i ↦ (z i).val)).mp
    apply (e.linearIndependent_iff (LinearMap.ker_eq_bot.mpr e.injective)).mp
    have hh := hy.units_smul (fun _ ↦ Units.mk0 ((j : ℝ)+1) hp.ne')
    change LinearIndependent ℝ (fun i ↦ ((j : ℝ)+1) • (((j : ℝ)+1)⁻¹ • y i)) at hh
    change LinearIndependent ℝ y
    simpa only [smul_inv_smul₀ hp.ne'] using hh
  have boxIntegral (j : ℕ) : (∫⁻ x, F j x ∂Measure.pi (fun _ ↦ volume)) = V^3 := by
    let t := (j : ℝ)+1
    have ht : 0 < t := by dsimp [t]; positivity
    let B (i : Fin 3) := ball (t • c i) (t*r)
    let U := densityBall n j
    have eqF : F j = (univ.pi B).indicator (fun _ ↦ (volume U)⁻¹ ^ 3) := by
      funext x
      by_cases hx : ∀ i, x i ∈ B i
      · simp [F,offTest, B, t, hx, U]
      · obtain ⟨i,hi⟩ := not_forall.mp hx
        rw [Set.indicator_of_notMem (by simpa [Set.mem_univ_pi] using hx)]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
    rw [eqF, lintegral_indicator (MeasurableSet.univ_pi fun i ↦ isOpen_ball.measurableSet),
      setLIntegral_const, Measure.pi_pi]
    have hv (i) : volume (B i) = V * volume U := by
      dsimp only [B,U,densityBall]
      rw [volume.addHaar_ball_of_pos _ (mul_pos ht hr),
        volume.addHaar_ball_of_pos _ ht, finrank_euclideanSpace_fin, mul_pow,
        ENNReal.ofReal_mul (pow_nonneg ht.le _)]
      dsimp [V,t]; ac_rfl
    change (volume U)⁻¹ ^ 3 * (∏ i, volume (B i)) = _
    simp only [hv, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]
    rw [mul_left_comm, ENNReal.inv_mul_cancel (show volume U ≠ 0 from (measure_ball_pos volume 0 ht).ne')
      measure_ball_lt_top.ne, mul_one]
  have value (j : ℕ) : (∫⁻ g in D, W j g ∂groupHaar n) = C * V^3 := by
    rw [domain, hC, lintegral_smul_measure, smul_eq_mul, boxIntegral]
  obtain ⟨K,hK⟩ := siegel_density_residue_class_bound n (by omega)
  let b (g : SL n) := (K : ℝ≥0∞)^3 * (2^3 + 2^3 * (densityWork n 0 g)^3)
  have hb : (∫⁻ g in D, b g ∂groupHaar n) ≠ ⊤ := by
    dsimp only [b]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top),
      lintegral_add_left measurable_const, setLIntegral_const,
      lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞)^3 ≠ ⊤)]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num) hf, ENNReal.mul_ne_top (by norm_num)
        (densityWork_unit_power_finite 3 (by decide) hn hd)⟩)
  have dom (j g) : W j g ≤ b g := by
    refine (bound j g).trans ((pow_le_pow_left' (hK j g) 3).trans ?_)
    rw [mul_pow]
    unfold b
    gcongr
    generalize densityWork n 0 g = a
    by_cases ha : a ≤ 1
    · have h : 1+a ≤ 2 := (add_le_add_right ha 1).trans_eq (by norm_num)
      exact (pow_le_pow_left' h 3).trans le_self_add
    · have h : 1+a ≤ 2*a := by rw [two_mul]; exact add_le_add_left (le_of_not_ge ha) a
      exact (pow_le_pow_left' h 3).trans (by rw [mul_pow]; exact le_add_self)
  have lim := tendsto_lintegral_of_dominated_convergence (μ := (groupHaar n).restrict D)
    (f := fun _ ↦ V^3) b (fun j ↦ (tupleWorkload_measurable (meas j)).comp measurable_quotient_mk'')
    (fun j ↦ Eventually.of_forall (dom j)) hb (Eventually.of_forall point)
  change Tendsto (fun j ↦ ∫⁻ g in D, W j g ∂groupHaar n) atTop _ at lim
  simp only [value, setLIntegral_const] at lim
  have he := tendsto_nhds_unique tendsto_const_nhds lim
  rw [mul_comm (V^3)] at he
  exact hC.trans (congrArg (· • Measure.pi (fun _ ↦ volume))
    ((ENNReal.mul_left_inj (pow_ne_zero _ V0) (ENNReal.pow_ne_top Vf)).mp he))

#print axioms rogers_three_frame_measure
end SigabaNeo.Rogers.Frame
