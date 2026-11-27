import Definitions.Def_LatticeAttack_Reduction_Rogers_PrimitiveOrbitCalibration

set_option autoImplicit true

open MeasureTheory Filter SigabaNeo.Rogers Set
open scoped ENNReal Topology

namespace SigabaNeo.Rogers

private theorem variableShear_le {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasureOnCompacts μ]
    (A : ℝ → E n → E n) (q : E n → ℝ) (hq : Measurable q)
    (hm : ∀ a, Measurable (A a)) (hc : ∀ x, Continuous (fun a ↦ A a x))
    (hp : ∀ a x, q (A a x) = q x) (hi : ∀ a, μ.map (A a) = μ)
    (f : ℝ → ℝ) (hf : StronglyMeasurable f) (s : Set (E n)) :
    μ ((fun x ↦ A (f (q x)) x) ⁻¹' s) ≤ μ s := by
  classical
  have simple (g : SimpleFunc ℝ ℝ) (U : Set (E n)) (hU : MeasurableSet U) :
      μ ((fun x ↦ A (g (q x)) x) ⁻¹' U) = μ U := by
    let B (a : ℝ) := (fun x ↦ g (q x)) ⁻¹' {a}
    have mb (a : ℝ) : MeasurableSet (B a) := (g.measurableSet_fiber a).preimage hq
    have split (V : Set (E n)) : V = ⋃ a ∈ g.range, V ∩ B a := by
      ext x
      simp [B, and_comm]
    have disj (V : Set (E n)) : (↑g.range : Set ℝ).PairwiseDisjoint (fun a ↦ V ∩ B a) := by
      intro a _ b _ hab
      exact Set.disjoint_left.mpr fun x hx hy ↦ hab (hx.2.symm.trans hy.2)
    let V := (fun x ↦ A (g (q x)) x) ⁻¹' U
    have eqv (a : ℝ) : V ∩ B a = A a ⁻¹' (U ∩ B a) := by
      ext x
      change (_ ∧ g (q x) = a) ↔ (_ ∧ g (q (A a x)) = a)
      rw [hp]
      exact and_congr_left fun h ↦ by simp [V, h]
    change μ V = μ U
    conv_lhs => rw [split V, measure_biUnion_finset (disj V) (fun a _ ↦ eqv a ▸ (hU.inter (mb a)).preimage (hm a))]
    conv_rhs => rw [split U, measure_biUnion_finset (disj U) (fun a _ ↦ hU.inter (mb a))]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [eqv, ← Measure.map_apply (hm a) (hU.inter (mb a)), hi]
  rw [s.measure_eq_iInf_isOpen μ]
  refine le_iInf fun U ↦ le_iInf fun hs ↦ le_iInf fun hU ↦ ?_
  let V (k : ℕ) := (fun x ↦ A (hf.approx k (q x)) x) ⁻¹' U
  let W (k : ℕ) := {x | ∀ l ≥ k, x ∈ V l}
  have mono : Monotone W := fun _ _ h _ hx l hl ↦ hx l (h.trans hl)
  calc
    _ ≤ μ (⋃ k, W k) := by
      apply measure_mono
      intro x hx
      exact mem_iUnion.mpr (eventually_atTop.mp (((hc x).continuousAt.tendsto.comp
        (hf.tendsto_approx (q x))).eventually (hU.mem_nhds (hs hx))))
    _ = _ := mono.measure_iUnion
    _ ≤ _ := iSup_le fun k ↦ (measure_mono (show W k ⊆ V k from fun _ hx ↦ hx k le_rfl)).trans
      (simple (hf.approx k) U hU.measurableSet).le

theorem sl_invariant_translate_on_coordinate_patch (n : ℕ) (_hn : 2 ≤ n) (μ : Measure (E n))
    (_hz : μ {0} = 0) (hf : IsFiniteMeasureOnCompacts μ)
    (hi : ∀ g : SL n, μ.map (fun x : E n ↦ WithLp.toLp 2 (g • WithLp.ofLp x)) = μ) :
    ∀ (i : Fin n) (t : ℝ) (j : Fin n), j ≠ i →
      (μ.map (t • EuclideanSpace.basisFun (Fin n) ℝ i + ·)).restrict {x | x j ≠ 0} =
        μ.restrict {x | x j ≠ 0} := by
  classical
  intro i t j hji
  let b := EuclideanSpace.basisFun (Fin n) ℝ i
  let A (a : ℝ) (x : E n) := (a * x j) • b + x
  have hj (r : ℝ) (x : E n) : (r • b + x) j = x j := by
    simp [b, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply, hji]
  have hm (a : ℝ) : Measurable (A a) :=
    (((continuous_const.mul (PiLp.continuous_apply 2 _ j)).smul continuous_const).add continuous_id).measurable
  have hiA (a : ℝ) : μ.map (A a) = μ := by
    convert hi (Matrix.SpecialLinearGroup.transvection hji.symm a) using 2
    funext x
    ext k
    by_cases hk : k = i <;> simp [A, b, Matrix.SpecialLinearGroup.smul_def,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.single_mulVec_eq,
      EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply, hk, add_comm]
  let P := {x : E n | x j ≠ 0}
  have leTr (r : ℝ) (s : Set (E n)) (hs : s ⊆ P) :
      μ ((r • b + ·) ⁻¹' s) ≤ μ s := by
    apply le_trans (measure_mono _) (variableShear_le μ A (fun x ↦ x j)
      (PiLp.continuous_apply 2 _ j).measurable hm (fun x ↦ by dsimp [A]; fun_prop)
      (fun a x ↦ hj _ x) hiA (fun y ↦ r / y) (measurable_const.div measurable_id).stronglyMeasurable s)
    intro x hx
    have h : x j ≠ 0 := by simpa only [P, mem_ofPred_eq, hj] using hs hx
    simpa [A, div_mul_cancel₀ _ h] using hx
  have mP : MeasurableSet P := (isClosed_eq (PiLp.continuous_apply 2 _ j) (continuous_const (y := (0 : ℝ)))).measurableSet.compl
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Measure.map_apply (measurable_const_add _) (hs.inter mP)]
  change μ ((t • b + ·) ⁻¹' (s ∩ P)) = μ (s ∩ P)
  apply le_antisymm (leTr t _ inter_subset_right)
  have rev := leTr (-t) ((t • b + ·) ⁻¹' (s ∩ P)) (fun x hx ↦ by
    have h := hx.2
    simpa only [P, mem_ofPred_eq, hj] using h)
  simpa [preimage_preimage, Function.comp_def, neg_smul] using rev

end SigabaNeo.Rogers
