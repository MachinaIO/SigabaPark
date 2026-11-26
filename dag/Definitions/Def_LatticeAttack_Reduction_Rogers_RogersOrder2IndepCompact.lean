import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2Assembly
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2IndepMeasure
import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2IndepSquare

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SigabaNeo.Rogers

private def pairTest (n j : ℕ) (x : Fin 2 → E n) :=
  densityTest n j (x 0) * densityTest n j (x 1)

private theorem pairTest_work (n j : ℕ) (g : SL n) :
    tupleWorkload (pairTest n j) (QuotientGroup.mk g) = (densityWork n j g)^2 := by
  let V := {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}
  let u := fun x : V ↦ densityTest n j x.val
  have h : densityWork n j g = ∑' v : V, u v :=
    (Equiv.funUnique (Fin 1) V).tsum_eq u
  rw [h, sq, ← ENNReal.tsum_mul_left]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [← tsum_prod]
  rw [← (finTwoArrowEquiv V).tsum_eq (fun p ↦ u p.2 * u p.1)]
  exact tsum_congr fun _ ↦ mul_comm _ _

theorem independentPairMeasure_finiteOnCompacts {n : ℕ} (hn : 2 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hfin : groupHaar n D ≠ ⊤) :
    IsFiniteMeasureOnCompacts (independentPairMeasure D) := by
  constructor
  intro K hK
  obtain ⟨r,hr⟩ := hK.isBounded.subset_ball 0
  obtain ⟨k,hk⟩ := exists_nat_gt r
  have ev := (densityWork_square_limit hn hd hfin).eventually (gt_mem_nhds hfin.lt_top)
  obtain ⟨j,hj,hj'⟩ := (ev.and (eventually_ge_atTop k)).exists
  let B := densityBall n j
  have sub : ∀ x ∈ K, ∀ i, x i ∈ B := by
    intro x hx i
    have hh := hr hx
    rw [Metric.mem_ball, dist_zero_right] at hh
    change dist (x i) 0 < (j : ℝ) + 1
    rw [dist_zero_right]
    have := norm_le_pi_norm x i
    have : (k : ℝ) ≤ j := by exact_mod_cast hj'
    linarith
  have m : Measurable (pairTest n j) :=
    ((densityTest_measurable n j).comp (measurable_pi_apply 0)).mul
      ((densityTest_measurable n j).comp (measurable_pi_apply 1))
  have htotal := domain_lintegral_tupleWorkload (groupHaar n) D m
  simp_rw [pairTest_work] at htotal
  have sumBound : (∫⁻ x, pairTest n j x ∂independentPairMeasure D) ≤
      ∫⁻ g in D, (densityWork n j g)^2 ∂groupHaar n := by
    rw [independentPairMeasure_lintegral D _ m, htotal]
    exact (CompleteLattice.summable.tsum_add_tsum_compl (s := orderTwoIndependent n)
      (f := orderTwoOrbit D (pairTest n j)) CompleteLattice.summable) ▸ le_self_add
  have hv : volume B ≠ 0 :=
    (Metric.measure_ball_pos volume _ (by positivity : 0 < (j : ℝ) + 1)).ne'
  have hv' : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have le (x) : K.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤ (volume B)^2 * pairTest n j x := by
    by_cases hx : x ∈ K
    · simp [hx, pairTest, densityTest, show x 0 ∈ densityBall n j from sub x hx 0,
        show x 1 ∈ densityBall n j from sub x hx 1, ← sq, ← mul_pow, B, ENNReal.mul_inv_cancel hv hv']
    · simp [hx]
  have h := lintegral_mono (μ := independentPairMeasure D) le
  rw [lintegral_indicator hK.measurableSet, setLIntegral_const, one_mul,
    lintegral_const_mul' _ _ (ENNReal.pow_ne_top hv')] at h
  exact lt_of_le_of_lt h (ENNReal.mul_ne_top (ENNReal.pow_ne_top hv') (sumBound.trans_lt hj).ne).lt_top

#print axioms independentPairMeasure_finiteOnCompacts

private def ballScale (n j : ℕ) : ℝ≥0∞ := ((j : ℝ≥0∞) + 1)^n

private lemma densityTest_scaled (n j : ℕ) (x : E n) :
    densityTest n j (((j+1 : ℕ) : ℝ) • x) = (ballScale n j)⁻¹ * densityTest n 0 x := by
  have hr : 0 < (j : ℝ) + 1 := by positivity
  have hmem : ((j+1 : ℕ) : ℝ) • x ∈ densityBall n j ↔ x ∈ densityBall n 0 := by
    simp [densityBall, norm_smul, abs_of_pos hr]
    constructor <;> intro h <;> nlinarith
  have hv : volume (densityBall n j) = ballScale n j * volume (densityBall n 0) := by
    simp [ballScale,densityBall,volume.addHaar_ball_of_pos _ hr,
      ENNReal.ofReal_pow hr.le, ENNReal.ofReal_add (by positivity : 0 ≤ (j : ℝ)) zero_le_one]
  by_cases hx : x ∈ densityBall n 0
  · simp only [densityTest, Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx), hv]
    exact ENNReal.mul_inv (Or.inr measure_ball_lt_top.ne) (Or.inl (by unfold ballScale; finiteness))
  · simp only [densityTest, Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mp hx), mul_zero]

private lemma measurable_pairTest (n j : ℕ) : Measurable (pairTest n j) :=
  ((densityTest_measurable n j).comp (measurable_pi_apply 0)).mul
    ((densityTest_measurable n j).comp (measurable_pi_apply 1))

private lemma line_scale {n q : ℕ} (j : ℕ) (A : Diagram 1 2 (q+1)) :
    (∫⁻ x, pairTest n j (orderTwoLine A x)) =
      (ballScale n j)⁻¹ * ∫⁻ x, pairTest n 0 (orderTwoLine A x) := by
  let u := fun x : E n ↦ pairTest n j (orderTwoLine A x)
  have hu : Measurable u := (measurable_pairTest n j).comp
    (Measurable.of_eval fun i ↦ measurable_const_smul _)
  have e := lintegral_dilation j u hu
  have w : dilationWeight n j = (ballScale n j)⁻¹ := by
    simp [dilationWeight, ballScale, abs_of_pos (by positivity : 0 < (j : ℝ)+1),
      ENNReal.ofReal_inv_of_pos (by positivity : 0 < ((j : ℝ)+1)^n),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (j : ℝ)+1),
      ENNReal.ofReal_add (by positivity : 0 ≤ (j : ℝ)) zero_le_one]
  have eval (x : E n) : u (((j+1 : ℕ) : ℝ) • x) =
      ((ballScale n j)⁻¹)^2 * pairTest n 0 (orderTwoLine A x) := by
    unfold u pairTest orderTwoLine
    simp only [smul_comm (A.entry 0 0 : ℝ), smul_comm (A.entry 0 1 : ℝ), densityTest_scaled]
    ring
  rw [w] at e
  simp_rw [eval] at e
  rw [lintegral_const_mul' _ _ (by unfold ballScale; finiteness)] at e
  have h0 : ballScale n j ≠ 0 := by unfold ballScale; positivity
  have hf : ballScale n j ≠ ⊤ := by unfold ballScale; finiteness
  have := congrArg (ballScale n j * ·) e
  simpa only [sq, ← mul_assoc, ENNReal.mul_inv_cancel h0 hf, one_mul, u] using this.symm

/-- Once proportionality to Lebesgue measure on frames is known, ball counts fix the scalar. -/
theorem independentPairMeasure_scalar_calibration {n : ℕ} (hn : 2 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    {C : ℝ≥0∞} (hC : independentPairMeasure D = C • Measure.pi (fun _ ↦ volume)) :
    C = groupHaar n D := by
  let M := groupHaar n D * orderTwoRankTerm (pairTest n 0) 0
  have total (j : ℕ) : (∫⁻ g in D, (densityWork n j g)^2 ∂groupHaar n) =
      C + (ballScale n j)⁻¹ * M := by
    simp_rw [← pairTest_work]
    rw [domain_lintegral_tupleWorkload _ _ (measurable_pairTest n j)]
    change (∑' z, orderTwoOrbit D (pairTest n j) z) = _
    rw [← CompleteLattice.summable.tsum_add_tsum_compl (s := orderTwoIndependent n)
        (f := orderTwoOrbit D (pairTest n j)) CompleteLattice.summable,
      ← independentPairMeasure_lintegral D _ (measurable_pairTest n j), hC,
      lintegral_smul_measure, smul_eq_mul,
      orderTwo_dependent n hn D hd hf _ (measurable_pairTest n j)]
    have unit : (∫⁻ x, pairTest n j x ∂Measure.pi (fun _ ↦ volume)) = 1 := by
      let f := densityTest n j
      have he := (measurePreserving_finTwoArrow (volume : Measure (E n))).lintegral_comp_emb
        MeasurableEquiv.finTwoArrow.measurableEmbedding (fun p ↦ f p.1 * f p.2)
      exact he.trans ((lintegral_prod_mul (densityTest_measurable n j).aemeasurable
        (densityTest_measurable n j).aemeasurable).trans (by simp [densityTest_unit]))
    rw [unit, mul_one]
    congr 1
    dsimp only [M]
    rw [orderTwo_rank_one n _ (measurable_pairTest n j), orderTwo_rank_one n _ (measurable_pairTest n 0)]
    simp_rw [line_scale j, ENNReal.tsum_mul_left]
    ac_rfl
  have hM : M ≠ ⊤ := by
    have h := densityWork_unit_square_finite hn hd
    rw [total 0] at h
    simpa [ballScale] using (ENNReal.add_ne_top.mp h).2
  have hlim : Tendsto (fun j ↦ (ballScale n j)⁻¹) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.pow (n := n)
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
    simpa [Function.comp_def, ballScale, ENNReal.inv_pow, show n ≠ 0 by omega] using h
  have h := (tendsto_const_nhds (x := C)).add
    (ENNReal.Tendsto.mul_const hlim (Or.inr hM))
  apply tendsto_nhds_unique _ (densityWork_square_limit hn hd hf)
  simpa [total] using h
#print axioms independentPairMeasure_scalar_calibration
end SigabaNeo.Rogers
