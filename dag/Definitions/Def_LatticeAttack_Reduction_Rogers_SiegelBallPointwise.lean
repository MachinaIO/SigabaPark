import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelDensityTests

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology Pointwise
namespace SigabaNeo.Rogers

private abbrev grid (n : ℕ) := Submodule.span ℤ (range (Pi.basisFun ℝ (Fin n)))

private def chart {n : ℕ} (g : SL n) : (Fin n → ℝ) ≃L[ℝ] E n :=
  g.toLin'.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin n) ℝ).symm

private theorem chart_preserves {n : ℕ} (g : SL n) : MeasurePreserving (chart g) := by
  apply (PiLp.volume_preserving_toLp (Fin n)).comp (g := WithLp.toLp 2)
  refine ⟨g.toLin'.toContinuousLinearEquiv.continuous.measurable, ?_⟩
  change Measure.map (Matrix.toLin' g.val) volume = volume
  simpa [g.property] using Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := g.val) (by rw [g.property]; norm_num)

private theorem chart_points {n : ℕ} (g : SL n) (x : Fin n → ℝ) :
    chart g x ∈ points (QuotientGroup.mk g) ↔ x ∈ grid n := by
  rw [points_mk, Module.Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr]
  change (∃ z : Fin n → ℤ, chart g (fun i ↦ (z i : ℝ)) = chart g x) ↔ _
  simp only [(chart g).injective.eq_iff, funext_iff]
  change (∃ z : Fin n → ℤ, ∀ i, (z i : ℝ) = x i) ↔ ∀ i, ∃ a : ℤ, (a : ℝ) = x i
  exact (Classical.skolem (p := fun i (a : ℤ) ↦ (a : ℝ) = x i)).symm

private def punctured (n : ℕ) := ball (0 : E n) 1 \ {0}

private theorem grid_count {n : ℕ} (hn : 2 ≤ n) (g : SL n) :
    let s := (chart g) ⁻¹' punctured n
    Tendsto (fun k : ℕ ↦ (Nat.card (s ∩ (k : ℝ)⁻¹ • grid n : Set _) : ℝ) / k ^ n)
      atTop (𝓝 (volume.real (ball (0 : E n) 1))) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hm : MeasurableSet (punctured n) := isOpen_ball.measurableSet.diff (measurableSet_singleton _)
  have hp := chart_preserves g
  have hv : volume.real ((chart g) ⁻¹' punctured n) = volume.real (ball (0 : E n) 1) := by
    rw [measureReal_def, hp.measure_preimage hm.nullMeasurableSet, punctured,
      measure_sdiff_null (measure_singleton _)]
    rfl
  rw [← hv]
  dsimp only
  conv => arg 1; ext k; arg 2; rw [← Fintype.card_fin n]
  refine tendsto_card_div_pow_atTop_volume
    ((chart g) ⁻¹' punctured n) ?_ ?_ ?_
  · exact (chart g).antilipschitzWith.isBounded_preimage (isBounded_ball.subset sdiff_subset)
  · exact hm.preimage (chart g).continuous.measurable
  · apply measure_mono_null ((chart g).continuous.frontier_preimage_subset _)
    rw [hp.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet]
    have hs : frontier (punctured n) ⊆ sphere 0 1 ∪ {0} := by
      unfold punctured
      rw [sdiff_eq, Set.inter_comm]
      grw [frontier_inter_subset, frontier_compl, inter_subset_left, inter_subset_right,
        frontier_subset_closure, closure_singleton, frontier_ball_subset_sphere]
      exact union_comm _ _ |>.le
    exact measure_mono_null hs (measure_union_null (volume.addHaar_sphere _ _) (measure_singleton _))

private theorem work_count {n : ℕ} (g : SL n) (j : ℕ) :
    let r := (j : ℝ) + 1
    let s := (chart g) ⁻¹' punctured n
    densityWork n j g = (Nat.card (s ∩ r⁻¹ • grid n : Set _) : ℝ≥0∞) /
      volume (densityBall n j) := by
  classical
  let r := (j : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let s := (chart g) ⁻¹' punctured n
  let A := {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}
  let B : Set A := {x | x.val ∈ densityBall n j}
  let T := (r • s ∩ grid n : Set _)
  let U := (s ∩ r⁻¹ • grid n : Set _)
  let eu : U ≃ T := (Equiv.smulRight hr.ne').subtypeEquiv fun x ↦ by
    simp [U, T, Equiv.smulRight_apply, smul_mem_smul_set_iff₀ hr.ne',
      mem_inv_smul_set_iff₀ hr.ne']
  let et : T ≃ B := ((chart g).toEquiv.subtypeEquiv (p := (· ∈ T))
    (q := fun y ↦ (y ∈ points (QuotientGroup.mk g) ∧ y ≠ 0) ∧ y ∈ densityBall n j)
    (fun x ↦ by
      change (x ∈ r • s ∧ x ∈ grid n) ↔ _
      rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
      change (((chart g) (r⁻¹ • x) ∈ punctured n) ∧ x ∈ grid n) ↔
        ((chart g x ∈ points _ ∧ chart g x ≠ 0) ∧ chart g x ∈ densityBall n j)
      simp [punctured, densityBall, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, inv_mul_lt_iff₀ hr, chart_points, hr.ne', r]; tauto)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have : Finite T := (ZSpan.setFinite_inter _ ((chart g).antilipschitzWith.isBounded_preimage
    (isBounded_ball.subset (sdiff_subset : punctured n ⊆ _)) |>.smul₀ r)).to_subtype
  have : Finite B := Finite.of_equiv _ et
  let f (x : A) := densityTest n j x.val
  change (∑' v : Fin 1 → A, f (v 0)) = _
  trans ∑' x : A, f x
  · exact (Equiv.funUnique (Fin 1) A).tsum_eq f
  change (∑' x : A, B.indicator (fun _ ↦ (volume (densityBall n j))⁻¹) x) = _
  let := Fintype.ofFinite B
  rw [← tsum_subtype, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change _ = (Nat.card U : ℝ≥0∞) / _
  rw [Nat.card_congr (eu.trans et), Nat.card_eq_fintype_card]
  rfl

theorem siegel_density_ball_pointwise (n : ℕ) (hn : 2 ≤ n) (g : SL n) :
    Tendsto (fun j ↦ densityWork n j g) atTop (𝓝 1) := by
  let V := volume.real (ball (0 : E n) 1)
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have h := ((grid_count hn g).comp (tendsto_add_atTop_nat 1)).div_const V
  have h' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  rw [show volume.real (ball (0 : E n) 1) / V = 1 from div_self hV.ne', ENNReal.ofReal_one] at h'
  apply h'.congr
  intro j
  rw [work_count]
  dsimp only [Function.comp_apply]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [ENNReal.ofReal_div_of_pos hV, ENNReal.ofReal_div_of_pos (by positivity)]
  simp [V, measureReal_def, ENNReal.ofReal_toReal measure_ball_lt_top.ne, densityBall,
    volume.addHaar_ball_of_pos _ (by positivity : 0 < (j : ℝ) + 1)]
  simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inr measure_ball_lt_top.ne)
    (Or.inl ENNReal.ofReal_ne_top), mul_assoc]

#print axioms siegel_density_ball_pointwise
end SigabaNeo.Rogers
