import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKFrameCompact

set_option autoImplicit true

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SigabaNeo.Rogers.Frame

abbrev FrameSpace (n k : ℕ) := Fin k → E n
def shear {n k : ℕ} (i j : Fin n) (t : ℝ) (x : FrameSpace n k) : FrameSpace n k :=
  fun a ↦ (t * x a j) • EuclideanSpace.basisFun (Fin n) ℝ i + x a

theorem shear_eval {n} (i j l : Fin n) (t : ℝ) (x : FrameSpace n k) (a : Fin k) :
    shear i j t x a l = (if l=i then t*x a j else 0) + x a l := by
  by_cases h : l=i <;> simp [shear, EuclideanSpace.basisFun_apply, PiLp.add_apply,
    PiLp.smul_apply, h]

theorem shear_meas {n k} (i j : Fin n) (t : ℝ) : Measurable (shear (k := k) i j t) := by
  unfold shear
  fun_prop

theorem shear_inv {n k} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    (frameMeasure (k := k) D).map (shear i j t) = frameMeasure (k := k) D := by
  convert frameMeasure_sl_invariant hd (Matrix.SpecialLinearGroup.transvection hij t) using 2
  funext x a
  ext l
  by_cases hk : l=i <;> simp [shear, Matrix.SpecialLinearGroup.smul_def,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.single_mulVec_eq,
    EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply, hk, add_comm]

theorem variableShear_le {n k : ℕ} (μ : Measure (FrameSpace n k)) [IsFiniteMeasureOnCompacts μ]
    (A : ℝ → FrameSpace n k → FrameSpace n k) (q : FrameSpace n k → ℝ) (hq : Measurable q)
    (hm : ∀ a, Measurable (A a)) (hc : ∀ x, Continuous (fun a ↦ A a x))
    (hp : ∀ a x, q (A a x) = q x) (hi : ∀ a, μ.map (A a) = μ)
    (f : ℝ → ℝ) (hf : StronglyMeasurable f) (s : Set (FrameSpace n k)) :
    μ ((fun x ↦ A (f (q x)) x) ⁻¹' s) ≤ μ s := by
  classical
  have simple (g : SimpleFunc ℝ ℝ) (U : Set (FrameSpace n k)) (hU : MeasurableSet U) :
      μ ((fun x ↦ A (g (q x)) x) ⁻¹' U) = μ U := by
    let B (a : ℝ) := (fun x ↦ g (q x)) ⁻¹' {a}
    have mb (a : ℝ) : MeasurableSet (B a) := (g.measurableSet_fiber a).preimage hq
    have split (V : Set (FrameSpace n k)) : V = ⋃ a ∈ g.range, V ∩ B a := by
      ext x
      simp [B, and_comm]
    have disj (V : Set (FrameSpace n k)) : (↑g.range : Set ℝ).PairwiseDisjoint (fun a ↦ V ∩ B a) := by
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



def rowVector {n k} (i : Fin n) (v : Fin k → ℝ) : FrameSpace n k :=
  fun a ↦ v a • EuclideanSpace.basisFun (Fin n) ℝ i

/-- Compose shears with coefficients that depend only on the rows other than the target. -/
theorem row_translate_of_coefficients {n k} {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    [IsFiniteMeasureOnCompacts (frameMeasure (k := k) D)]
    (i : Fin n) (v : Fin k → ℝ) (p : Fin n → FrameSpace n k → ℝ)
    (hm : ∀ j, Measurable (p j))
    (hrow : ∀ j x y, (∀ a l, l ≠ i → x a l = y a l) → p j x = p j y)
    (hsolve : ∀ᵐ x ∂frameMeasure D, ∀ a, ∑ j ∈ Finset.univ.erase i, p j x * x a j = v a)
    (S : Set (FrameSpace n k)) :
    frameMeasure D ((rowVector i v + ·) ⁻¹' S) ≤ frameMeasure D S := by
  let μ := frameMeasure (k := k) D
  let A (s : Finset (Fin n)) (x : FrameSpace n k) :=
    rowVector i (fun a ↦ ∑ j ∈ s, p j x * x a j) + x
  have outside (s) (x : FrameSpace n k) (a l) (hl : l ≠ i) : A s x a l = x a l := by
    simp [A, rowVector, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply, hl]
  have bound (s : Finset (Fin n)) (hs : i ∉ s) (U : Set (FrameSpace n k)) :
      μ (A s ⁻¹' U) ≤ μ U := by
    induction s using Finset.induction_on generalizing U with
    | empty =>
      have hzero : rowVector i (fun _ : Fin k ↦ (0 : ℝ)) = 0 := by funext a; simp [rowVector]
      have he : A ∅ = id := by funext x; simp only [A, Finset.sum_empty, hzero, zero_add, id_eq]
      rw [he]; rfl
    | insert j s hj ih =>
      have hi : i ≠ j := fun h ↦ hs (h ▸ Finset.mem_insert_self _ _)
      let B (x : FrameSpace n k) := shear i j (p j x) x
      have inv (t) (x : FrameSpace n k) : p j (shear i j t x) = p j x :=
        hrow _ _ _ (by intro a l hl; simp [shear_eval, hl])
      have hB := variableShear_le μ (shear i j) (p j) (hm j) (shear_meas i j)
        (fun x ↦ by unfold shear; fun_prop) inv (shear_inv hd hi) id
        continuous_id.stronglyMeasurable U
      have he : A (insert j s) = B ∘ A s := by
        funext x a
        ext l
        change A (insert j s) x a l = shear i j (p j (A s x)) (A s x) a l
        rw [shear_eval, hrow j _ x (outside s x), outside s x a j hi.symm]
        by_cases hl : l = i
        · subst l
          simp [A, rowVector, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply,
            Finset.sum_insert hj, add_assoc]
        · simp [outside _ _ _ _ hl, hl]
      rw [he]
      exact (ih (fun h ↦ hs (Finset.mem_insert_of_mem h)) (B ⁻¹' U)).trans hB
  refine (measure_mono_ae ?_).trans (bound (Finset.univ.erase i) (Finset.notMem_erase _ _) S)
  filter_upwards [hsolve] with x hx
  simp only [Set.mem_preimage, A]
  simp only [hx]; exact le_rfl

theorem frameMeasure_proportional_of_row {n k} (hk : 0 < k) (hn : k < n) {D : Set (SL n)}
    (hd : IsFundamentalDomain (integerGroup n).op D (groupHaar n)) (hf : groupHaar n D ≠ ⊤)
    (hle : ∀ (i : Fin n) (v : Fin k → ℝ) (s : Set (FrameSpace n k)),
      frameMeasure D ((rowVector i v + ·) ⁻¹' s) ≤ frameMeasure D s) :
    ∃ C : ℝ≥0∞, frameMeasure (k := k) D = C • Measure.pi (fun _ ↦ volume) := by
  let μ := frameMeasure (k := k) D
  let := frameMeasure_finiteOnCompacts hk hn hd hf
  have row (i : Fin n) (v : Fin k → ℝ) : μ.map (rowVector i v + ·) = μ := by
    ext s hs
    rw [Measure.map_apply (measurable_const_add _) hs]
    apply le_antisymm (hle i v s)
    have h := hle i (-v) ((rowVector i v + ·) ⁻¹' s)
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
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin k ↦
    (volume : Measure (E n)))⟩

end SigabaNeo.Rogers.Frame
