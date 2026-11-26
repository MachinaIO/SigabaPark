import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration

set_option autoImplicit true

open MeasureTheory SigabaNeo.Rogers

namespace SigabaNeo.Rogers

theorem sl_invariant_coordinate_axis_null (n : ℕ) (hn : 2 ≤ n) (μ : Measure (E n))
    (hz : μ {0} = 0) (hf : IsFiniteMeasureOnCompacts μ)
    (hi : ∀ g : SL n, μ.map (fun x : E n ↦ WithLp.toLp 2 (g • WithLp.ofLp x)) = μ) :
    ∀ i : Fin n, μ {x | ∀ j ≠ i, x j = 0} = 0 := by
  classical
  intro i
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  let S (t : ℝ) := {x : E n | x i ≠ 0 ∧ x j = t * x i}
  have hm (t : ℝ) : MeasurableSet (S t) := by
    exact ((isClosed_eq (PiLp.continuous_apply 2 _ i) continuous_const).measurableSet.compl).inter
      (isClosed_eq (PiLp.continuous_apply 2 _ j)
        (continuous_const.mul (PiLp.continuous_apply 2 _ i))).measurableSet
  have hd : Pairwise (fun s t ↦ Disjoint (S s) (S t)) := by
    intro s t h
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact h (mul_right_cancel₀ hx.1 (hx.2.symm.trans hy.2))
  obtain ⟨t, ht⟩ : ∃ t, μ (S t) = 0 := by
    by_contra! h
    apply Set.not_countable_univ (α := ℝ)
    exact (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hm hd).mono
      (fun t _ ↦ bot_lt_iff_ne_bot.mpr (h t))
  let g : SL n := Matrix.SpecialLinearGroup.transvection hji t
  let A := fun x : E n ↦ WithLp.toLp 2 (g • WithLp.ofLp x)
  have hA : Measurable A := by
    have hc : Continuous (fun z ↦ g.val.mulVec z) := by
      unfold Matrix.mulVec dotProduct
      fun_prop
    exact ((PiLp.continuous_toLp 2 _).comp (hc.comp (PiLp.continuous_ofLp 2 _))).measurable
  have hpre : μ (A ⁻¹' S t) = 0 := by
    rw [← Measure.map_apply hA (hm t)]
    change (μ.map (fun x : E n ↦ WithLp.toLp 2 (g • WithLp.ofLp x))) (S t) = 0
    rw [hi g]
    exact ht
  apply measure_mono_null (t := {0} ∪ A ⁻¹' S t) _ (measure_union_null hz hpre)
  intro x hx
  by_cases hxi : x i = 0
  · left
    ext k
    by_cases hk : k = i
    · subst k
      exact hxi
    · exact hx k hk
  · right
    change ((g • WithLp.ofLp x) i ≠ 0 ∧
      (g • WithLp.ofLp x) j = t * (g • WithLp.ofLp x) i)
    simp [g, Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_mulVec, Matrix.single_mulVec_eq, Pi.single_eq_of_ne hji.symm, hx j hji, hxi]

end SigabaNeo.Rogers
