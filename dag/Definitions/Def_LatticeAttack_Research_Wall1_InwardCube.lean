import Definitions.Def_LatticeAttack_Planted_Volume

set_option autoImplicit true

/-! Inward halves of unit cubes give the sharpened integer-ball count of Part 172. -/

noncomputable section
namespace SigabaNeo.Wall1.DualExit
open MeasureTheory Metric Set
open scoped BigOperators

/-- The volume enclosing the inward half-cubes centered in the radius-`r` integer ball. -/
def inwardVolume (ι : Type*) [Fintype ι] (r : ℝ) : ℝ :=
  Real.sqrt (r ^ 2 + Fintype.card ι / 4) ^ Fintype.card ι *
    volume.real (ball (0 : EuclideanSpace ℝ ι) 1)

/-- Any finite collection of integer points in the closed ball, including the origin if desired.
Reflection gives each inward portion at least half a cube, even at the origin. -/
theorem inward_half_cube {ι : Type*} [Fintype ι] (T : Finset (ι → ℤ)) (r : ℝ)
    (hr : ∀ z ∈ T, ∑ i, (z i : ℝ) ^ 2 ≤ r ^ 2) :
    (T.card : ℝ) / 2 ≤ inwardVolume ι r := by
  classical
  let C : Set (ι → ℝ) := univ.pi fun _ ↦ Ioo (-1/2) (1/2)
  let c (z : ι → ℤ) : ι → ℝ := fun i ↦ z i
  let H (z : ι → ℤ) := C ∩ {x : ι → ℝ | ∑ i, c z i * x i ≤ 0}
  let cell (z : ι → ℤ) := (fun x ↦ -c z + x) ⁻¹' H z
  have mC : MeasurableSet C :=
    (measurableSet_pi (to_countable _)).2 (.inl fun _ _ ↦ measurableSet_Ioo)
  have mH z : MeasurableSet (H z) := mC.inter (measurableSet_le (by fun_prop) measurable_const)
  have mc z : MeasurableSet (cell z) := (mH z).preimage (by fun_prop)
  have vC : volume C = 1 := by norm_num [C, volume_pi_pi, Real.volume_Ioo]
  have finH z : volume (H z) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [vC]) (measure_mono inter_subset_left)
  have vcell z : volume (cell z) = volume (H z) := measure_preimage_add _ _ _
  have half z : 1 / 2 ≤ volume.real (cell z) := by
    have incl : C ⊆ H z ∪ Neg.neg ⁻¹' H z := by
      intro x hx
      by_cases h : ∑ i, c z i * x i ≤ 0
      · exact Or.inl ⟨hx, h⟩
      · refine Or.inr ⟨fun i _ ↦ ?_, ?_⟩
        · obtain ⟨hl, hu⟩ := hx i (mem_univ _)
          change -1/2 < -(x i) ∧ -(x i) < 1/2
          constructor <;> linarith
        · change ∑ i, c z i * (-x i) ≤ 0
          simpa only [mul_neg, Finset.sum_neg_distrib, neg_nonpos] using
            (show 0 ≤ ∑ i, c z i * x i from le_of_not_ge h)
    have vm := measure_mono (μ := volume) incl |>.trans (measure_union_le _ _)
    rw [vC, Measure.measure_preimage_neg] at vm
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finH z, finH z⟩) vm
    rw [ENNReal.toReal_one, ENNReal.toReal_add (finH z) (finH z)] at hh
    rw [Measure.real, vcell]
    linarith
  have dj : PairwiseDisjoint (T : Set (ι → ℤ)) cell := by
    intro z _ w _ hne
    apply Set.disjoint_left.mpr
    intro x hz hw
    apply hne
    funext i
    obtain ⟨a,b⟩ := hz.1 i (mem_univ _)
    obtain ⟨d,e⟩ := hw.1 i (mem_univ _)
    change -1/2 < -(z i : ℝ) + x i at a
    change -(z i : ℝ) + x i < 1/2 at b
    change -1/2 < -(w i : ℝ) + x i at d
    change -(w i : ℝ) + x i < 1/2 at e
    have h₁ : z i < w i + 1 := by exact_mod_cast (by linarith : (z i : ℝ) < w i + 1)
    have h₂ : w i < z i + 1 := by exact_mod_cast (by linarith : (w i : ℝ) < z i + 1)
    omega
  let s := Real.sqrt (r ^ 2 + Fintype.card ι / 4)
  let D := closedBall (0 : EuclideanSpace ℝ ι) s
  have incl : (⋃ z ∈ T, cell z) ⊆ WithLp.toLp 2 ⁻¹' D := by
    intro x hx
    obtain ⟨z, hz, h⟩ := mem_iUnion₂.mp hx
    let u := -c z + x
    have hd : ∑ i, c z i * u i ≤ 0 := h.2
    have hu : ∑ i, u i ^ 2 ≤ ∑ _ : ι, (1/2 : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨lo, hi⟩ := h.1 i (mem_univ _)
      apply sq_le_sq' <;> linarith [show -1/2 < u i from lo, show u i < 1/2 from hi]
    have hxsum : ∑ i, x i ^ 2 = (∑ i, (z i : ℝ) ^ 2) +
        2 * (∑ i, c z i * u i) + ∑ i, u i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change x i ^ 2 = ((z i : ℝ) ^ 2 + 2 * ((z i : ℝ) * (- (z i : ℝ) + x i))) +
        (- (z i : ℝ) + x i) ^ 2
      ring
    change dist (WithLp.toLp 2 x) 0 ≤ s
    rw [dist_zero_right, ← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
      EuclideanSpace.real_norm_sq_eq, Real.sq_sqrt (by positivity)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
    change ∑ i, x i ^ 2 ≤ _
    linarith [hr z hz]
  have upper := measure_mono (μ := volume) incl
  rw [(PiLp.volume_preserving_toLp ι).measure_preimage measurableSet_closedBall.nullMeasurableSet]
    at upper
  have bound := ENNReal.toReal_mono measure_closedBall_lt_top.ne upper
  change volume.real _ ≤ volume.real (closedBall (0 : EuclideanSpace ℝ ι) s) at bound
  rw [measureReal_biUnion_finset dj (fun z _ ↦ mc z) (fun z _ ↦ vcell z ▸ finH z),
    Measure.addHaar_real_closedBall volume _ (Real.sqrt_nonneg _)] at bound
  calc
    _ = ∑ _ ∈ T, (1/2 : ℝ) := by simp; ring
    _ ≤ _ := (Finset.sum_le_sum fun z _ ↦ half z).trans bound
    _ = _ := by simp [inwardVolume]

end SigabaNeo.Wall1.DualExit

#print axioms SigabaNeo.Wall1.DualExit.inward_half_cube
