module

public import Mathlib

set_option autoImplicit true

@[expose] public section

/-! The Han admissibility conditions and the nonnegative workload boundary follow
Laarhoven, arXiv:2609.13635v1, HanAdmissible and QuotientHanRogers. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SigabaNeo.Rogers

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev SL (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) ℝ

def integerGroup (n : ℕ) : Subgroup (SL n) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)).range

abbrev LatticeSpace (n : ℕ) := SL n ⧸ integerGroup n

/-- Generate the set of lattice points before summing. This counts each geometric tuple once. -/
def points {n : ℕ} (L : LatticeSpace n) : Set (E n) :=
  Set.range fun z : Fin n → ℤ ↦ WithLp.toLp 2
    ((Quotient.out L : SL n) • (fun i ↦ (z i : ℝ)))

/-- Every representative gives the same geometric lattice. -/
theorem points_mk {n : ℕ} (g : SL n) :
    points (QuotientGroup.mk g) =
      Set.range (fun z : Fin n → ℤ ↦ WithLp.toLp 2 (g • (fun i ↦ (z i : ℝ)))) := by
  let g' := (QuotientGroup.mk g : LatticeSpace n).out
  have he : (QuotientGroup.mk g : LatticeSpace n) = QuotientGroup.mk g' :=
    (Quotient.out_eq _).symm
  obtain ⟨γ, hγ⟩ := QuotientGroup.eq.mp he
  have hg : g' = g * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ := by
    rw [hγ, ← mul_assoc, mul_inv_cancel, one_mul]
  have hc (z : Fin n → ℤ) : (fun i ↦ ((γ • z) i : ℝ)) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ • (fun i ↦ (z i : ℝ)) := by
    funext i
    exact RingHom.map_mulVec (Int.castRingHom ℝ) γ.val z i
  change Set.range (fun z : Fin n → ℤ ↦ WithLp.toLp 2 (g' • (fun i ↦ (z i : ℝ)))) = _
  rw [hg]
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨γ • z, by dsimp only; rw [hc, mul_smul]⟩
  · rintro ⟨z,rfl⟩
    exact ⟨γ⁻¹ • z, by dsimp only; rw [mul_smul, ← hc, smul_inv_smul]⟩

def tupleWorkload {n k : ℕ} (F : (Fin k → E n) → ℝ≥0∞) (L : LatticeSpace n) : ℝ≥0∞ :=
  ∑' z : Fin k → {x : E n // x ∈ points L ∧ x ≠ 0}, F fun i ↦ z i

structure Diagram (r k q : ℕ) where
  entry : Matrix (Fin r) (Fin k) ℤ
  pivot : Fin r → Fin k
  increasing : StrictMono pivot
  first : ∀ i : Fin r, i.val = 0 → (pivot i).val = 0
  nonzeroColumn : ∀ j, ∃ i, entry i j ≠ 0
  pivotColumn : ∀ i a, entry i (pivot a) = if i = a then (q : ℤ) else 0
  echelon : ∀ i j, j < pivot i → entry i j = 0
  primitive : ∀ d : ℕ, (∀ i j, (d : ℤ) ∣ entry i j) → d = 1

theorem fullRank_denominator {k q : ℕ} (D : Diagram k k q) : q = 1 := by
  apply D.primitive
  intro i j
  have h : D.pivot j = j := le_antisymm (D.increasing.le_id j) (D.increasing.id_le j)
  have he := D.pivotColumn i j
  rw [h] at he
  rw [he]
  split <;> simp

abbrev Coefficients := ∀ k, (r : Fin k) → (q : ℕ) → Diagram (r.val + 1) k (q + 1) → ℝ≥0∞

def diagramSum {n k : ℕ} (c : Coefficients) (F : (Fin k → E n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ r : Fin k, ∑' q : ℕ, ∑' D : Diagram (r.val + 1) k (q + 1),
    c k r q D * ∫⁻ v : Fin (r.val + 1) → E n,
      F (fun j ↦ ((q + 1 : ℕ) : ℝ)⁻¹ • ∑ i, (D.entry i j : ℝ) • v i)
      ∂Measure.pi (fun _ ↦ volume)

def Admissible {n k : ℕ} (F : (Fin k → E n) → ℝ≥0∞) : Prop :=
  Measurable F ∧ (∃ M < ∞, ∀ z, F z ≤ M) ∧
  (∃ B : ℝ, ∀ z, F z ≠ 0 → ∀ i, ‖z i‖ ≤ B) ∧ (∀ z, F z ≠ 0 → ∀ i, z i ≠ 0)

scoped instance (n : ℕ) : MeasurableSpace (SL n) :=
  borel {A : Matrix (Fin n) (Fin n) ℝ // A.det = 1}

structure ClassicalRogersFormula {n : ℕ} (ν : Measure (LatticeSpace n)) (c : Coefficients) :
    Prop where
  bound : ∀ k r q D, c k r q D ≤ ENNReal.ofReal (((q + 1 : ℕ) : ℝ) ^ (-(n : ℝ)))
  unit : ∀ k r D, c k r 0 D = 1
  formula : ∀ k, 1 ≤ k → k < n → ∀ F : (Fin k → E n) → ℝ≥0∞, Admissible F →
    (∫⁻ L, tupleWorkload F L ∂ν) = diagramSum c F

theorem sieveWorkload {n k : ℕ} {ν : Measure (LatticeSpace n)} {c : Coefficients}
    (h : ClassicalRogersFormula ν c) (hk : k ∈ Finset.Icc 1 3) (hn : k < n)
    {F : (Fin k → E n) → ℝ≥0∞} (hF : Admissible F) :
    (∫⁻ L, tupleWorkload F L ∂ν) = diagramSum c F :=
  h.formula k (Finset.mem_Icc.mp hk).1 hn F hF

private def orderOne : Diagram 1 1 1 where
  entry := fun _ _ ↦ 1
  pivot := id
  increasing := strictMono_id
  first := fun _ h ↦ h
  nonzeroColumn := fun _ ↦ ⟨0, by simp⟩
  pivotColumn := by intro i a; simp [Subsingleton.elim i a]
  echelon := by intro i j h; exact (lt_irrefl i (Subsingleton.elim j i ▸ h)).elim
  primitive := by
    intro d hd
    have h := hd 0 0
    exact Nat.dvd_one.mp (by exact_mod_cast h)

private theorem eq_orderOne (D : Diagram 1 1 1) : D = orderOne := by
  have he : D.entry = fun _ _ ↦ 1 := by
    funext i j
    simpa [Subsingleton.elim (D.pivot j) j, Subsingleton.elim i j] using D.pivotColumn i j
  have hpi : D.pivot = id := Subsingleton.elim _ _
  cases D
  congr

/-- The sole surviving order-one diagram gives the Lebesgue integral with coefficient one. -/
theorem diagramSum_one {n : ℕ} {c : Coefficients} (hc : ∀ D, c 1 0 0 D = 1)
    (f : E n → ℝ≥0∞) :
    diagramSum c (fun v : Fin 1 → E n ↦ f (v 0)) = ∫⁻ x, f x := by
  classical
  unfold diagramSum
  rw [Fin.sum_univ_one, tsum_eq_single 0]
  · simp only [Fin.val_zero, zero_add, Nat.reduceAdd] at *
    rw [tsum_eq_single orderOne]
    · simp [hc, orderOne]
      exact (measurePreserving_funUnique (volume : Measure (E n)) (Fin 1)).lintegral_comp_emb
        (MeasurableEquiv.funUnique (Fin 1) (E n)).measurableEmbedding f
    · intro D hD
      exact (hD (eq_orderOne D)).elim
  · intro q hq
    apply tsum_eq_zero_iff.mpr
    intro D
    have h := fullRank_denominator (k := 1) D
    omega

theorem siegel_of_rogers {n : ℕ} {ν : Measure (LatticeSpace n)} {c : Coefficients}
    (h : ClassicalRogersFormula ν c) (hn : 1 < n) (f : E n → ℝ≥0∞)
    (hf : Admissible (fun v : Fin 1 → E n ↦ f (v 0))) :
    (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L ∂ν) = ∫⁻ x, f x :=
  (h.formula 1 le_rfl hn _ hf).trans (diagramSum_one (h.unit 1 0) f)

/-- Push the normalized restriction of group measure to representatives down to lattices. -/
def domainProbability {n : ℕ} (μ : Measure (SL n)) (D : Set (SL n)) : Measure (LatticeSpace n) :=
  (μ D)⁻¹ • (μ.restrict D).map QuotientGroup.mk

theorem domainProbability_probability {n : ℕ} (μ : Measure (SL n)) (D : Set (SL n))
    (hpos : μ D ≠ 0) (hfin : μ D ≠ ∞) : IsProbabilityMeasure (domainProbability μ D) := by
  constructor
  rw [domainProbability, Measure.smul_apply, Measure.map_apply measurable_quotient_mk''
    MeasurableSet.univ]
  simpa using ENNReal.inv_mul_cancel hpos hfin

local instance (n : ℕ) : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))

local instance (n : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))

local instance (n : ℕ) : Countable (Matrix (Fin n) (Fin n) ℤ) :=
  inferInstanceAs (Countable (Fin n → Fin n → ℤ))

local instance (n : ℕ) : BorelSpace (SL n) := ⟨rfl⟩

local instance (n : ℕ) : PolishSpace (SL n) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace

local instance (n : ℕ) : LocallyCompactSpace (SL n) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

def groupHaar (n : ℕ) : Measure (SL n) := Measure.haar

theorem groupHaar_rightInvariant_of_perfect {n : ℕ} (h : commutator (SL n) = ⊤) :
    (groupHaar n).IsMulRightInvariant := by
  change (Measure.haar : Measure (SL n)).IsMulRightInvariant
  constructor
  intro g
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul]
  have hg : g ∈ commutator (SL n) := by simp [h]
  have hk := Abelianization.commutator_le_ker
    (Measure.modularCharacter (G := SL n)).toHomUnits hg
  have he := congrArg Units.val (MonoidHom.mem_ker.mp hk)
  change Measure.modularCharacterFun g = 1 at he
  rw [he, one_smul]

theorem groupHaar_two_rightInvariant : (groupHaar 2).IsMulRightInvariant :=
  groupHaar_rightInvariant_of_perfect
    (Matrix.SL2.commutator_eq_top (a := (2:ℝ)) (by norm_num) (by norm_num))

section
open Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement
private theorem trans_mem {n : ℕ} {i j : Fin n} (h : i ≠ j) (a : ℝ) :
    SpecialLinearGroup.transvection h a ∈ commutator (SL n) := by
  let d := diag2n h (2 : ℝ) (by norm_num)
  let t := SpecialLinearGroup.transvection h (a/3)
  have he : ⁅d,t⁆ = SpecialLinearGroup.transvection h a := by
    rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    dsimp only [t]
    rw [← transvection_add]
    apply Subtype.ext
    ext k l
    simp only [d, coe_mul, diag2n_coe, transvection_coe, mul_add, add_mul,
      Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.one_apply, single_apply]
    split_ifs <;> grind
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem sl_commutator_eq_top {n : ℕ} (hn : 2 ≤ n) : commutator (SL n) = ⊤ := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  apply top_unique
  intro g _
  refine diagonal_transvection_induction' (fun x ↦ x ∈ commutator (SL n)) g ?_
    (fun _ _ ↦ trans_mem) (fun _ _ ↦ mul_mem)
  intro i j h c hc
  let T := SpecialLinearGroup.transvection h (F := ℝ)
  let S := SpecialLinearGroup.transvection h.symm (F := ℝ)
  have he : diag2n h c hc = T c * S (-c⁻¹) * T c * T (-1) * S 1 * T (-1) := by
    apply Subtype.ext
    simp only [T, S, coe_mul, transvection_coe, mul_add, add_mul, mul_one, one_mul,
      single_mul_single_same, single_mul_single_of_ne _ _ _ _ h,
      single_mul_single_of_ne _ _ _ _ h.symm, add_zero]
    ext k l
    simp only [diag2n_coe, diagonal_apply, Matrix.add_apply, Matrix.one_apply, single_apply]
    split_ifs <;> grind
  rw [he]
  repeat' apply mul_mem
  all_goals exact trans_mem _ _

theorem groupHaar_rightInvariant (n : ℕ) : (groupHaar n).IsMulRightInvariant := by
  apply groupHaar_rightInvariant_of_perfect
  by_cases hn : 2 ≤ n
  · exact sl_commutator_eq_top hn
  · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
    exact Subsingleton.elim _ _

end

private def latticeVector {n : ℕ} (g : SL n) (z : Fin n → ℤ) : E n :=
  WithLp.toLp 2 (g • (fun i ↦ (z i : ℝ)))

private theorem latticeVector_injective {n : ℕ} (g : SL n) : Function.Injective (latticeVector g) := by
  intro z w h
  have h' := congrArg WithLp.ofLp h
  have he : (fun i ↦ (z i : ℝ)) = (fun i ↦ (w i : ℝ)) := MulAction.injective g h'
  funext i
  exact_mod_cast congrFun he i

private abbrev NonzeroVector (n : ℕ) := {z : Fin n → ℤ // z ≠ 0}

private theorem tupleWorkload_mk {n k : ℕ} (F : (Fin k → E n) → ℝ≥0∞) (g : SL n) :
    tupleWorkload F (QuotientGroup.mk g) =
      ∑' z : Fin k → NonzeroVector n, F (fun i ↦ latticeVector g (z i)) := by
  classical
  have hz (g : SL n) : latticeVector g 0 = 0 := by
    simp [latticeVector, Matrix.SpecialLinearGroup.smul_def]
    exact Matrix.mulVec_zero _
  let e : NonzeroVector n → {x : E n // x ∈ points (QuotientGroup.mk g) ∧ x ≠ 0} := fun z ↦
    ⟨latticeVector g z, by rw [points_mk]; exact ⟨z, rfl⟩,
      fun h ↦ z.property (latticeVector_injective g (h.trans (hz g).symm))⟩
  have he : Function.Bijective e := by
    constructor
    · intro z w h
      exact Subtype.ext (latticeVector_injective g (congrArg Subtype.val h))
    · intro ⟨x, hx, hx'⟩
      rw [points_mk] at hx
      obtain ⟨z, rfl⟩ := hx
      exact ⟨⟨z, fun h ↦ hx' (h ▸ hz g)⟩, rfl⟩
  let E := Equiv.piCongrRight (fun _ : Fin k ↦ Equiv.ofBijective e he)
  exact (E.tsum_eq (fun z ↦ F (fun i ↦ (z i).val))).symm

private theorem measurable_tuple_term {n k : ℕ} {F : (Fin k → E n) → ℝ≥0∞}
    (hF : Measurable F) (z : Fin k → NonzeroVector n) :
    Measurable (fun g : SL n ↦ F (fun i ↦ latticeVector g (z i))) := by
  apply hF.comp
  apply Measurable.of_eval
  intro i
  apply Continuous.measurable
  change Continuous (fun g : SL n ↦ WithLp.toLp 2 (g.val.mulVec (fun j ↦ ((z i).val j : ℝ))))
  apply (PiLp.continuous_toLp 2 _).comp
  unfold Matrix.mulVec dotProduct
  fun_prop

theorem tupleWorkload_measurable {n k : ℕ} {F : (Fin k → E n) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (tupleWorkload F) := by
  apply QuotientGroup.measurable_from_quotient.mpr
  change Measurable (fun g : SL n ↦ tupleWorkload F (QuotientGroup.mk g))
  simp_rw [tupleWorkload_mk]
  exact Measurable.tsum (measurable_tuple_term hF)

/-- Expand the domain integral into orbital integrals indexed by integer tuples. -/
theorem domain_lintegral_tupleWorkload {n k : ℕ} (μ : Measure (SL n)) (D : Set (SL n))
    {F : (Fin k → E n) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g in D, tupleWorkload F (QuotientGroup.mk g) ∂μ) =
      ∑' z : Fin k → {v : Fin n → ℤ // v ≠ 0},
        ∫⁻ g in D, F (fun i ↦ WithLp.toLp 2 (g • fun j ↦ ((z i).val j : ℝ))) ∂μ := by
  simp_rw [tupleWorkload_mk]
  exact lintegral_tsum (fun z ↦ (measurable_tuple_term hF z).aemeasurable)

theorem domain_mass_ne_zero {n : ℕ} (μ : Measure (SL n)) [μ.IsMulRightInvariant]
    (hμ : μ ≠ 0) {D : Set (SL n)} (hD : IsFundamentalDomain (integerGroup n).op D μ) :
    μ D ≠ 0 := by
  have : Countable (Matrix (Fin n) (Fin n) ℤ) := inferInstanceAs (Countable (Fin n → Fin n → ℤ))
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  have : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) := Subtype.val_injective.countable
  have : Countable (integerGroup n) := φ.rangeRestrict_surjective.countable
  have : Countable (integerGroup n).op := (integerGroup n).equivOp.surjective.countable
  exact hD.measure_ne_zero hμ

open Set in
/-- A Borel arithmetic transversal, obtained by taking the first quotient chart
meeting each fiber in a countable cover. -/
theorem arithmetic_domain (n : ℕ) :
    ∃ D : Set (SL n), MeasurableSet D ∧
      IsFundamentalDomain (integerGroup n).op D (groupHaar n) ∧ groupHaar n D ≠ 0 := by
  classical
  let q : SL n → LatticeSpace n := QuotientGroup.mk
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have hd : IsDiscrete (integerGroup n : Set (SL n)) :=
    he.specialLinearGroup_map.isInducing.isDiscrete_range
  have hq := (integerGroup n).isQuotientCoveringMap hd
  choose c hc heq using hq.isCoveringMap.isLocalHomeomorph
  obtain ⟨T, hT, hcov⟩ := TopologicalSpace.countable_cover_nhds
    (fun x ↦ (c x).open_source.mem_nhds (hc x))
  have covers (x : SL n) : ∃ t ∈ T, x ∈ (c t).source := by
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (hcov.ge (mem_univ x))
    exact ⟨i, hi, hx⟩
  have : Nonempty T := let ⟨t, ht, _⟩ := covers 1; ⟨⟨t, ht⟩⟩
  have := hT.to_subtype
  obtain ⟨a, ha⟩ := exists_surjective_nat T
  let U := fun i ↦ (c (a i)).source
  let V := fun i ↦ (c (a i)).target
  have lift (i : ℕ) {y} (hy : y ∈ V i) : ∃ x ∈ U i, q x = y := by
    refine ⟨_, (c (a i)).map_target hy, ?_⟩
    exact (congrFun (heq (a i)) _).trans ((c (a i)).right_inv hy)
  have someChart (x : SL n) : ∃ i, q x ∈ V i := by
    obtain ⟨t, ht, hx⟩ := covers x
    obtain ⟨i, hi⟩ := ha ⟨t, ht⟩
    refine ⟨i, ?_⟩
    simpa only [V, hi, q, heq t] using (c t).map_source hx
  let D := ⋃ i : ℕ, U i \ ⋃ j < i, q ⁻¹' V j
  have hD : MeasurableSet D := MeasurableSet.iUnion fun i ↦
    (c (a i)).open_source.measurableSet.diff (MeasurableSet.iUnion fun j ↦
      MeasurableSet.iUnion fun _ ↦
        ((c (a j)).open_target.preimage hq.continuous).measurableSet)
  have FD : IsFundamentalDomain (integerGroup n).op D (groupHaar n) := by
    apply IsFundamentalDomain.mk' hD.nullMeasurableSet
    intro x
    let i := Nat.find (someChart x)
    obtain ⟨y, hy, hyq⟩ := lift i (Nat.find_spec (someChart x))
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp hyq
    change g • x = y at hg
    refine ⟨g, ?_, ?_⟩
    · change g • x ∈ D
      rw [hg]
      exact mem_iUnion.mpr ⟨i, hy, by
        simpa only [mem_iUnion, mem_preimage, hyq, not_exists] using
          (fun j (hj : j < i) ↦ Nat.find_min (someChart x) hj)⟩
    · intro k hk
      obtain ⟨j, hj, hprev⟩ := mem_iUnion.mp hk
      have hkq : q (k • x) = q x := hq.map_smul k
      have hjq : q x ∈ V j := by
        rw [← hkq]
        simpa only [q, heq (a j)] using (c (a j)).map_source hj
      have hij : i ≤ j := Nat.find_min' _ hjq
      have hji : j ≤ i := le_of_not_gt fun hij' ↦ hprev
        (mem_iUnion₂.mpr ⟨i, hij', by simpa only [mem_preimage, hkq] using Nat.find_spec (someChart x)⟩)
      have hidx := le_antisymm hij hji
      have hxy : k • x = g • x := by
        rw [hg]
        apply (c (a i)).injOn (hidx.symm ▸ hj) hy
        simpa only [← heq (a i)] using hkq.trans hyq.symm
      exact hq.isCancelSMul.right_cancel' _ _ _ hxy
  let := groupHaar_rightInvariant n
  exact ⟨D, hD, FD, domain_mass_ne_zero (groupHaar n) (NeZero.ne (Measure.haar : Measure (SL n))) FD⟩

#print axioms arithmetic_domain

open Set in
open scoped Pointwise in
/-- Every arithmetic fundamental domain has mass at most that of any set whose
integer translates cover the group, allowing overlaps in a Siegel set. -/
theorem arithmetic_domain_mass_le {n : ℕ} {D S : Set (SL n)}
    (hD : IsFundamentalDomain (integerGroup n).op D (groupHaar n))
    (hS : ∀ x : SL n, ∃ g : (integerGroup n).op, x ∈ g • S) :
    groupHaar n D ≤ groupHaar n S := by
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  have : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) := Subtype.val_injective.countable
  have : Countable (integerGroup n) := φ.rangeRestrict_surjective.countable
  have : Countable (integerGroup n).op := (integerGroup n).equivOp.surjective.countable
  let := groupHaar_rightInvariant n
  rw [hD.measure_eq_tsum S]
  refine (measure_mono (t := ⋃ g : (integerGroup n).op, g • S ∩ D) ?_).trans
    (measure_iUnion_le _)
  intro x hx
  obtain ⟨g, hg⟩ := hS x
  exact mem_iUnion.mpr ⟨g, hg, hx⟩

/-- The diagonal integral in logarithmic simple-root coordinates, for positive weights.
For SL(n) the weight on the k-th simple root is k(n-k), with 1 ≤ k < n. -/
theorem siegel_diagonal_integral {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (c : ℝ) :
    (∫⁻ t : Fin d → ℝ, ENNReal.ofReal (∏ i, Real.exp (-w i * t i))
      ∂Measure.pi (fun _ ↦ volume.restrict (Set.Ioi c))) =
      ENNReal.ofReal (∏ i, Real.exp (-w i * c) / w i) := by
  have hi (i : Fin d) := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (hw i)) c
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod_dep hi)
    (Filter.Eventually.of_forall fun _ ↦ Finset.prod_nonneg fun _ _ ↦ (Real.exp_pos _).le),
    integral_fintype_prod_eq_prod (fun (i : Fin d) (t : ℝ) ↦ Real.exp (-w i * t))]
  simp_rw [integral_exp_mul_Ioi (neg_lt_zero.mpr (hw _))]
  simp

#print axioms siegel_diagonal_integral
#print axioms arithmetic_domain_mass_le

theorem domainProbability_invariant {n : ℕ} (μ : Measure (SL n))
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {D : Set (SL n)}
    (hD : IsFundamentalDomain (integerGroup n).op D μ) :
    SMulInvariantMeasure (SL n) (LatticeSpace n) (domainProbability μ D) := by
  let φ := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin n)
  have : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) :=
    Subtype.val_injective.countable
  have : Countable (integerGroup n) := φ.rangeRestrict_surjective.countable
  have he : Topology.IsClosedEmbedding (Int.castRingHom ℝ) := Int.isClosedEmbedding_coe_real
  have : IsClosed (integerGroup n : Set (SL n)) := he.specialLinearGroup_map.isClosed_range
  have : HasFundamentalDomain (integerGroup n).op (SL n) μ := ⟨⟨D,hD⟩⟩
  let ν : Measure (LatticeSpace n) := (μ.restrict D).map QuotientGroup.mk
  have : QuotientMeasureEqMeasurePreimage μ ν := hD.quotientMeasureEqMeasurePreimage_quotientMeasure
  have : SMulInvariantMeasure (SL n) (LatticeSpace n) ν :=
    QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient μ
  change SMulInvariantMeasure _ _ ((μ D)⁻¹ • ν)
  infer_instance

/-- Unnormalized unfolding on a domain suffices, with its actual covolume as factor. -/
theorem siegel_of_domain_unfolding {n : ℕ} (μ : Measure (SL n)) (D : Set (SL n))
    (hpos : μ D ≠ 0) (hfin : μ D ≠ ∞) (f : E n → ℝ≥0∞)
    (hm : Measurable (tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))))
    (hu : ∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂μ = μ D * ∫⁻ x, f x) :
    (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L ∂domainProbability μ D) =
      ∫⁻ x, f x := by
  rw [domainProbability, lintegral_smul_measure, lintegral_map hm measurable_quotient_mk'',
    smul_eq_mul, hu, ← mul_assoc, ENNReal.inv_mul_cancel hpos hfin, one_mul]

theorem siegel_of_measurable_unfolding {n : ℕ} (μ : Measure (SL n)) [μ.IsMulRightInvariant]
    (hμ : μ ≠ 0) {D : Set (SL n)} (hD : IsFundamentalDomain (integerGroup n).op D μ)
    (hfin : μ D ≠ ∞) (f : E n → ℝ≥0∞) (hf : Measurable f)
    (hu : ∫⁻ g in D, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0))
      (QuotientGroup.mk g) ∂μ = μ D * ∫⁻ x, f x) :
    (∫⁻ L, tupleWorkload (fun v : Fin 1 → E n ↦ f (v 0)) L ∂domainProbability μ D) =
      ∫⁻ x, f x :=
  siegel_of_domain_unfolding μ D (domain_mass_ne_zero μ hμ hD) hfin f
    (tupleWorkload_measurable (hf.comp (measurable_pi_apply 0))) hu

#print axioms domain_lintegral_tupleWorkload
#print axioms tupleWorkload_measurable
#print axioms domain_mass_ne_zero
#print axioms siegel_of_measurable_unfolding
#print axioms groupHaar_rightInvariant_of_perfect
#print axioms sl_commutator_eq_top
#print axioms groupHaar_rightInvariant
#print axioms groupHaar_two_rightInvariant

end SigabaNeo.Rogers
