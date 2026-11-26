import Definitions.Def_LatticeAttack_Reduction_Rogers_SiegelDensityTests

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology Pointwise
namespace SigabaNeo.Rogers.Frame

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


/-- Normalized count test on a dilate of a ball disjoint from the origin. -/
def offTest {n} (c : E n) (r : ℝ) (j : ℕ) : E n → ℝ≥0∞ :=
  (ball (((j : ℝ) + 1) • c) (((j : ℝ) + 1) * r)).indicator
    (fun _ ↦ (volume (densityBall n j))⁻¹)

def offWork {n} (c : E n) (r : ℝ) (j : ℕ) (g : SL n) :=
  tupleWorkload (fun v : Fin 1 → E n ↦ offTest c r j (v 0)) (QuotientGroup.mk g)

theorem off_mem {n} (c x : E n) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    x ∈ ball (t • c) (t * r) ↔ t⁻¹ • x ∈ ball c r := by
  have h : c = t⁻¹ • (t • c) := (inv_smul_smul₀ ht.ne' c).symm
  change dist x (t • c) < t * r ↔ dist (t⁻¹ • x) c < r
  conv_rhs => rw [h, dist_smul₀]
  simp [abs_of_pos ht, Real.norm_eq_abs, inv_mul_lt_iff₀ ht]

private theorem grid_count {n : ℕ} (hn : 2 ≤ n) (g : SL n) (c : E n) (r : ℝ) :
    let s := (chart g) ⁻¹' ball c r
    Tendsto (fun k : ℕ ↦ (Nat.card (s ∩ (k : ℝ)⁻¹ • grid n : Set _) : ℝ) / k ^ n)
      atTop (𝓝 (volume.real (ball c r))) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hm : MeasurableSet (ball c r) := isOpen_ball.measurableSet
  have hp := chart_preserves g
  have hv : volume.real ((chart g) ⁻¹' ball c r) = volume.real (ball c r) :=
    congrArg ENNReal.toReal (hp.measure_preimage hm.nullMeasurableSet)
  rw [← hv]
  dsimp only
  conv => arg 1; ext k; arg 2; rw [← Fintype.card_fin n]
  refine tendsto_card_div_pow_atTop_volume
    ((chart g) ⁻¹' ball c r) ?_ ?_ ?_
  · exact (chart g).antilipschitzWith.isBounded_preimage isBounded_ball
  · exact hm.preimage (chart g).continuous.measurable
  · apply measure_mono_null ((chart g).continuous.frontier_preimage_subset _)
    rw [hp.measure_preimage isClosed_frontier.measurableSet.nullMeasurableSet]
    exact measure_mono_null frontier_ball_subset_sphere (volume.addHaar_sphere _ _)

private theorem work_count {n : ℕ} (g : SL n) (j : ℕ) (c : E n) (δ : ℝ) (hc : 0 ∉ ball c δ) :
    let r := (j : ℝ) + 1
    let s := (chart g) ⁻¹' ball c δ
    offWork c δ j g = (Nat.card (s ∩ r⁻¹ • grid n : Set _) : ℝ≥0∞) /
      volume (densityBall n j) := by
  classical
  let r := (j : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let s := (chart g) ⁻¹' ball c δ
  let A := {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0}
  let B : Set A := {x | x.val ∈ ball (r • c) (r * δ)}
  let T := (r • s ∩ grid n : Set _)
  let U := (s ∩ r⁻¹ • grid n : Set _)
  let eu : U ≃ T := (Equiv.smulRight hr.ne').subtypeEquiv fun x ↦ by
    simp [U, T, Equiv.smulRight_apply, smul_mem_smul_set_iff₀ hr.ne',
      mem_inv_smul_set_iff₀ hr.ne']
  let et : T ≃ B := ((chart g).toEquiv.subtypeEquiv (p := (· ∈ T))
    (q := fun y ↦ (y ∈ points (QuotientGroup.mk g) ∧ y ≠ 0) ∧ y ∈ ball (r • c) (r * δ))
    (fun x ↦ by
      change (x ∈ r • s ∧ x ∈ grid n) ↔ _
      rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
      change (((chart g) (r⁻¹ • x) ∈ ball c δ) ∧ x ∈ grid n) ↔
        ((chart g x ∈ points _ ∧ chart g x ≠ 0) ∧ chart g x ∈ ball (r • c) (r * δ))
      rw [map_smul, off_mem c _ δ hr, chart_points]
      constructor
      · rintro ⟨hb,hg⟩
        exact ⟨⟨hg, fun hz ↦ hc (by simpa [hz] using hb)⟩, hb⟩
      · tauto)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have : Finite T := (ZSpan.setFinite_inter _ ((chart g).antilipschitzWith.isBounded_preimage
    isBounded_ball |>.smul₀ r)).to_subtype
  have : Finite B := Finite.of_equiv _ et
  let f (x : A) := offTest c δ j x.val
  change (∑' v : Fin 1 → A, f (v 0)) = _
  trans ∑' x : A, f x
  · exact (Equiv.funUnique (Fin 1) A).tsum_eq f
  change (∑' x : A, B.indicator (fun _ ↦ (volume (densityBall n j))⁻¹) x) = _
  let := Fintype.ofFinite B
  rw [← tsum_subtype, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change _ = (Nat.card U : ℝ≥0∞) / _
  rw [Nat.card_congr (eu.trans et), Nat.card_eq_fintype_card]
  rfl

theorem offWork_limit (n : ℕ) (hn : 2 ≤ n) (g : SL n) (c : E n) (r : ℝ) (hc : 0 ∉ ball c r) :
    Tendsto (fun j ↦ offWork c r j g) atTop (𝓝 (volume (ball c r) / volume (ball (0 : E n) 1))) := by
  let V := volume.real (ball (0 : E n) 1)
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have h := ((grid_count hn g c r).comp (tendsto_add_atTop_nat 1)).div_const V
  have h' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  rw [ENNReal.ofReal_div_of_pos hV] at h'
  simp only [V, measureReal_def, ENNReal.ofReal_toReal measure_ball_lt_top.ne] at h'
  apply h'.congr
  intro j
  rw [work_count g j c r hc]
  dsimp only [Function.comp_apply]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [ENNReal.ofReal_div_of_pos (show 0 < (volume (ball (0 : E n) 1)).toReal from hV),
    ENNReal.ofReal_div_of_pos (by positivity)]
  simp [ENNReal.ofReal_toReal measure_ball_lt_top.ne, densityBall,
    volume.addHaar_ball_of_pos _ (by positivity : 0 < (j : ℝ) + 1)]
  simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inr measure_ball_lt_top.ne)
    (Or.inl ENNReal.ofReal_ne_top), mul_assoc]

end SigabaNeo.Rogers.Frame
