import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrder2IndepCompact

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SigabaNeo.Rogers

private abbrev FrameSpace (n : ℕ) := Fin 2 → E n
private def minor {n : ℕ} (p q : Fin n) (x : FrameSpace n) :=
  x 0 p * x 1 q - x 1 p * x 0 q

private def shear {n : ℕ} (i j : Fin n) (t : ℝ) (x : FrameSpace n) : FrameSpace n :=
  fun a ↦ (t * x a j) • EuclideanSpace.basisFun (Fin n) ℝ i + x a

private lemma shear_eval {n} (i j k : Fin n) (t : ℝ) (x : FrameSpace n) (a : Fin 2) :
    shear i j t x a k = (if k=i then t*x a j else 0) + x a k := by
  by_cases h : k=i <;> simp [shear, EuclideanSpace.basisFun_apply, PiLp.add_apply,
    PiLp.smul_apply, h]

private lemma shear_meas {n} (i j : Fin n) (t : ℝ) : Measurable (shear i j t) := by
  unfold shear
  fun_prop

private lemma shear_inv {n} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    (independentPairMeasure D).map (shear i j t) = independentPairMeasure D := by
  convert independentPairMeasure_sl_invariant hd (Matrix.SpecialLinearGroup.transvection hij t) using 2
  funext x a
  ext k
  by_cases hk : k=i <;> simp [shear, Matrix.SpecialLinearGroup.smul_def,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply, hk, add_comm]

private lemma minor_meas {n} (i j : Fin n) : Measurable (minor i j) := by
  unfold minor
  fun_prop

private lemma minor_spread {n} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    [IsFiniteMeasureOnCompacts (independentPairMeasure D)]
    (i j k : Fin n) (hij : i ≠ j) :
    ∀ᵐ x ∂independentPairMeasure D, minor i j x = 0 → minor k j x = 0 := by
  classical
  by_cases hik : i = k
  · subst k; simp
  let μ := independentPairMeasure D
  let S (t : ℝ) := {x : FrameSpace n | minor k j x ≠ 0 ∧ minor i j x = t * minor k j x}
  have hm (t : ℝ) : MeasurableSet (S t) :=
    ((minor_meas k j (measurableSet_singleton 0)).compl).inter
      (measurableSet_eq_fun (minor_meas i j) (measurable_const.mul (minor_meas k j)))
  have disj : Pairwise (fun s t ↦ Disjoint (S s) (S t)) := by
    intro s t h
    exact Set.disjoint_left.mpr fun x hx hy ↦ h (mul_right_cancel₀ hx.1 (hx.2.symm.trans hy.2))
  obtain ⟨t,ht⟩ : ∃ t, μ (S t) = 0 := by
    by_contra! h
    exact Set.not_countable_univ (α := ℝ)
      ((Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hm disj).mono
        (fun t _ ↦ bot_lt_iff_ne_bot.mpr (h t)))
  have hz : μ (shear i k t ⁻¹' S t) = 0 := by
    rw [← Measure.map_apply (shear_meas _ _ _) (hm t)]
    simpa only [μ, shear_inv hd hik] using ht
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx h
  by_contra hk
  apply hx
  change minor k j _ ≠ 0 ∧ minor i j _ = _
  simp only [minor, shear_eval, ite_eq_right (Ne.symm hik), ite_eq_right hij.symm, ite_true, eq_self, zero_add] at *
  exact ⟨hk, by linear_combination h⟩

private lemma minor_swap {n} (i j : Fin n) (x : FrameSpace n) :
    minor j i x = - minor i j x := by unfold minor; ring

private lemma minor_nonzero_ae {n} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    [IsFiniteMeasureOnCompacts (independentPairMeasure D)] {i j : Fin n} (hij : i ≠ j) :
    ∀ᵐ x ∂independentPairMeasure D, minor i j x ≠ 0 := by
  have spread : ∀ᵐ x ∂independentPairMeasure D, ∀ a b c, a ≠ b →
      minor a b x = 0 → minor c b x = 0 := by
    simpa only [ae_all_iff] using (fun a b c ↦ show
      ∀ᵐ x ∂independentPairMeasure D, a ≠ b → minor a b x = 0 → minor c b x = 0 from
        by by_cases h : a ≠ b; simpa [h] using minor_spread hd a b c h; simp [h])
  filter_upwards [spread, independentPairMeasure_ae_independent D] with x hs hx h
  have col (a) := hs i j a hij h
  have allm (a b) : minor a b x = 0 := by
    by_cases hb : b = j
    · subst b; exact col a
    have h' := minor_swap b j x
    exact hs j b a (Ne.symm hb) (by rw [h', col, neg_zero])
  obtain ⟨a,ha⟩ : ∃ a, x 0 a ≠ 0 := by
    by_contra! hh
    exact hx.ne_zero 0 (by ext a; simpa using hh a)
  apply ha (Fintype.linearIndependent_iff.mp hx ![-x 1 a, x 0 a] ?_ 1)
  ext b
  simp [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply]
  have he := allm a b
  unfold minor at he
  linear_combination he

private theorem variableShear_le {n : ℕ} (μ : Measure (FrameSpace n)) [IsFiniteMeasureOnCompacts μ]
    (A : ℝ → FrameSpace n → FrameSpace n) (q : FrameSpace n → ℝ) (hq : Measurable q)
    (hm : ∀ a, Measurable (A a)) (hc : ∀ x, Continuous (fun a ↦ A a x))
    (hp : ∀ a x, q (A a x) = q x) (hi : ∀ a, μ.map (A a) = μ)
    (f : ℝ → ℝ) (hf : StronglyMeasurable f) (s : Set (FrameSpace n)) :
    μ ((fun x ↦ A (f (q x)) x) ⁻¹' s) ≤ μ s := by
  classical
  have simple (g : SimpleFunc ℝ ℝ) (U : Set (FrameSpace n)) (hU : MeasurableSet U) :
      μ ((fun x ↦ A (g (q x)) x) ⁻¹' U) = μ U := by
    let B (a : ℝ) := (fun x ↦ g (q x)) ⁻¹' {a}
    have mb (a : ℝ) : MeasurableSet (B a) := (g.measurableSet_fiber a).preimage hq
    have split (V : Set (FrameSpace n)) : V = ⋃ a ∈ g.range, V ∩ B a := by
      ext x
      simp [B, and_comm]
    have disj (V : Set (FrameSpace n)) : (↑g.range : Set ℝ).PairwiseDisjoint (fun a ↦ V ∩ B a) := by
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



private def rowVector {n} (i : Fin n) (v : Fin 2 → ℝ) : FrameSpace n :=
  fun a ↦ v a • EuclideanSpace.basisFun (Fin n) ℝ i

private lemma row_translate_le {n} (hn : 2 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    [IsFiniteMeasureOnCompacts (independentPairMeasure D)] (i : Fin n) (v : Fin 2 → ℝ)
    (s : Set (FrameSpace n)) :
    independentPairMeasure D ((rowVector i v + ·) ⁻¹' s) ≤ independentPairMeasure D s := by
  let μ := independentPairMeasure D
  obtain ⟨j,hji,_⟩ := Fin.exists_ne_and_ne_of_two_lt i i hn
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  let P (x : FrameSpace n) := (v 0 * x 1 k - v 1 * x 0 k) / minor j k x
  let Q (x : FrameSpace n) := (x 0 j * v 1 - x 1 j * v 0) / minor j k x
  have aux (l : Fin n) (hli : l ≠ i) (q : FrameSpace n → ℝ) (hq : Measurable q)
      (inv : ∀ t x, q (shear i l t x) = q x) (S : Set (FrameSpace n)) :
      μ ((fun x ↦ shear i l (q x) x) ⁻¹' S) ≤ μ S :=
    variableShear_le μ (shear i l) q hq (shear_meas i l)
      (fun x ↦ by unfold shear; fun_prop) inv (shear_inv hd hli.symm) id
      continuous_id.stronglyMeasurable S
  have Pinv (l : Fin n) (t : ℝ) (x : FrameSpace n) : P (shear i l t x) = P x := by
    simp [P, minor, shear_eval, hji, hki]
  have Qinv (l : Fin n) (t : ℝ) (x : FrameSpace n) : Q (shear i l t x) = Q x := by
    simp [Q, minor, shear_eval, hji, hki]
  let A (x : FrameSpace n) := shear i j (P x) x
  let B (x : FrameSpace n) := shear i k (Q x) x
  have hle : μ (A ⁻¹' (B ⁻¹' s)) ≤ μ s :=
    (aux j hji P (by unfold P minor; fun_prop) (Pinv j) _).trans
      (aux k hki Q (by unfold Q minor; fun_prop) (Qinv k) _)
  refine (measure_mono_ae ?_).trans hle
  filter_upwards [minor_nonzero_ae hd hkj.symm] with x hx
  change rowVector i v + x ∈ s → B (A x) ∈ s
  suffices he : B (A x) = rowVector i v + x by rw [he]; exact id
  funext a
  ext l
  change shear i k (Q (A x)) (A x) a l = (v a • EuclideanSpace.basisFun (Fin n) ℝ i + x a) l
  simp only [A, Qinv, shear_eval]
  by_cases hl : l = i
  · subst l
    simp [EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply, hki, P, Q]
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> field_simp [hx] <;> unfold minor <;> ring
  · simp [hl, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply]

theorem independentPairMeasure_proportional {n} (hn : 2 < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤) :
    ∃ C : ℝ≥0∞, independentPairMeasure D = C • Measure.pi (fun _ ↦ volume) := by
  let μ := independentPairMeasure D
  let := independentPairMeasure_finiteOnCompacts hn hd hf
  have row (i : Fin n) (v : Fin 2 → ℝ) : μ.map (rowVector i v + ·) = μ := by
    ext s hs
    rw [Measure.map_apply (measurable_const_add _) hs]
    apply le_antisymm (row_translate_le hn hd i v s)
    have h := row_translate_le hn hd i (-v) ((rowVector i v + ·) ⁻¹' s)
    have he : rowVector i (-v) = -rowVector i v := by funext a; simp [rowVector]
    simpa [he, preimage_preimage, Function.comp_def] using h
  have : μ.IsAddLeftInvariant := by
    constructor
    intro x
    let v (i : Fin n) := rowVector i (fun a ↦ x a i)
    have sums (s : Finset (Fin n)) : μ.map ((∑ i ∈ s, v i) + ·) = μ := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his ih =>
        rw [Finset.sum_insert his]
        have h := Measure.map_map (measurable_const_add (v i))
          (measurable_const_add (∑ j ∈ s, v j)) (μ := μ)
        simpa only [ih, row, Function.comp_def, ← add_assoc, v] using h.symm
    have he : ∑ i, v i = x := by
      funext a
      rw [Finset.sum_apply]
      exact (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr _
    simpa only [he] using sums Finset.univ
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin 2 ↦
    (volume : Measure (E n)))⟩

theorem rogers_two_independent (n : ℕ) (hn : 2 < n) (D : Set (SL n))
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (F : (Fin 2 → E n) → ℝ≥0∞) (hF : Admissible F) :
    (∑' z : orderTwoIndependent n, orderTwoOrbit D F z.val) =
      groupHaar n D * ∫⁻ v, F v ∂Measure.pi (fun _ ↦ volume) := by
  obtain ⟨C,hC⟩ := independentPairMeasure_proportional hn hd hf
  rw [← independentPairMeasure_lintegral D F hF.1, hC, lintegral_smul_measure, smul_eq_mul,
    independentPairMeasure_scalar_calibration hn hd hf hC]

#print axioms rogers_two_independent
end SigabaNeo.Rogers
