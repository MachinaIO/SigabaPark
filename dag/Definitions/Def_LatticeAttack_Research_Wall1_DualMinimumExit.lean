import Definitions.Def_LatticeAttack_Research_Wall1_RestartGraphDual
import Definitions.Def_LatticeAttack_Research_Wall1_InwardCube

set_option autoImplicit true

/-! The first-moment exit of Parts 142 and 172 on one uniform restart design. -/

noncomputable section
namespace SigabaNeo.Wall1.DualExit
open QaryMembership Finset MeasureTheory
open scoped Classical BigOperators

variable {m n q : ℕ} [Fact q.Prime]

private theorem prime_pos : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos

/-- A strict exit in the metric dual of the raw graph. -/
def rawExit (A : Design m n q) (R : ℝ) : Prop :=
  ∃ x ∈ metricDual (rawGraph A), x ≠ 0 ∧ ‖x‖ < R

private theorem eligible (A : Design m n q) (z : Point m n) (hz : dual A z)
    (hne : vector q z ≠ 0) (hs : ‖vector q z‖ < 1) : reduce q z.1 ≠ 0 := by
  intro h
  have hb : reduce q z.2 = 0 := by simpa [dual, h] using hz.symm
  apply hne
  ext i
  have hd : (q : ℤ) ∣ numerator z i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    cases i with
    | inl i => exact congrFun h i
    | inr j => simpa [numerator, reduce] using congrArg Neg.neg (congrFun hb j)
  obtain ⟨k, hk⟩ := hd
  have hv : vector q z i = (k : ℝ) := by
    change (numerator z i : ℝ) / q = _
    simp [hk, (prime_pos (q := q)).ne']
  have hsmall := (PiLp.norm_apply_le (vector q z) i).trans_lt hs
  rw [hv, Real.norm_eq_abs] at hsmall
  have hki : |k| < 1 := by exact_mod_cast hsmall
  have he : k = 0 := by by_contra hne'; exact (Int.one_le_abs hne').not_gt hki
  simpa [he] using hv

/-- Eligible signed numerators, with the strict radius of the exit. -/
def candidates (m n q : ℕ) (R : ℝ) : Finset (Point m n) :=
  ((SigabaNeo.Planted.integerBall (ι := Coord m n) (q * R)).map numerator.symm.toEmbedding).filter
    (fun z ↦ reduce q z.1 ≠ 0 ∧ ‖vector q z‖ < R)

private theorem mem_candidates {R : ℝ} (hR : 0 ≤ R) (z : Point m n) :
    z ∈ candidates m n q R ↔ reduce q z.1 ≠ 0 ∧ ‖vector q z‖ < R := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  rintro ⟨hm, hs⟩
  refine mem_filter.mpr ⟨mem_map.mpr ⟨numerator z, ?_, numerator.symm_apply_apply z⟩, hm, hs⟩
  apply (SigabaNeo.Planted.mem_integerBall (mul_nonneg prime_pos.le hR) _).mpr
  constructor
  · intro h
    apply hm
    funext i
    have hh : z.1 i = 0 := congrFun h (.inl i)
    simp [reduce, hh]
  · have hn := (sq_le_sq₀ (norm_nonneg _) hR).mpr hs.le
    rw [EuclideanSpace.real_norm_sq_eq] at hn
    change (∑ i, ((numerator z i : ℝ) / q)^2) ≤ _ at hn
    simp_rw [div_pow] at hn
    rw [← sum_div] at hn
    rw [mul_pow, mul_comm]
    exact (div_le_iff₀ (pow_pos prime_pos 2 : 0 < (q : ℝ)^2)).mp hn

theorem rawExit_iff {R : ℝ} (hR : 0 ≤ R) (h1 : R ≤ 1) (A : Design m n q) :
    rawExit A R ↔ (members dual (candidates m n q R) A).Nonempty := by
  constructor
  · rintro ⟨x, hx, hn, hs⟩
    obtain ⟨z, rfl⟩ := exists_numerator A hx
    have hd := (vector_mem_iff A z).mp hx
    exact ⟨z, mem_filter.mpr ⟨(mem_candidates hR z).mpr ⟨eligible A z hd hn (hs.trans_le h1),
      hs⟩, hd⟩⟩
  · rintro ⟨z, hz⟩
    obtain ⟨hm, hd⟩ := mem_filter.mp hz
    obtain ⟨he, hs⟩ := (mem_candidates hR z).mp hm
    refine ⟨vector q z, (vector_mem_iff A z).mpr hd, ?_, hs⟩
    intro h
    apply he
    funext i
    have hi := congrArg (fun x : Space m n ↦ x (.inl i)) h
    change (z.1 i : ℝ) / q = 0 at hi
    have hi' : (z.1 i : ℝ) = 0 := (div_eq_zero_iff.mp hi).resolve_right prime_pos.ne'
    have hi'' : z.1 i = 0 := by exact_mod_cast hi'
    simp [reduce, hi'']

/-- Uniform expected number of eligible signed hits, before pairing opposite vectors. -/
theorem signed_first_moment {R : ℝ} (hR : 0 ≤ R) :
    (∑ A : Design m n q, ((members dual (candidates m n q R) A).card : ℝ)) /
      Fintype.card (Design m n q) = (candidates m n q R).card / (q : ℝ)^n := by
  have h := (dual_counts (candidates m n q R)
    (fun z hz ↦ ((mem_candidates hR z).mp hz).1)).1
  rw [card_univ] at h
  have htot : (0 : ℝ) < Fintype.card (Design m n q) := by exact_mod_cast Fintype.card_pos
  apply (div_eq_div_iff htot.ne' (pow_ne_zero _ prime_pos.ne')).mpr
  exact_mod_cast h

/-- The signed first moment, divided by two using the opposite-pair symmetry. -/
theorem probability_le_candidates {R : ℝ} (hR : 0 ≤ R) (h1 : R ≤ 1) :
    probability (fun A : Design m n q ↦ rawExit A R) ≤
      (candidates m n q R).card / 2 / (q : ℝ)^n := by
  let S := candidates m n q R
  have hz : ∀ z ∈ S, reduce q z.1 ≠ 0 := fun z hz ↦ ((mem_candidates hR z).mp hz).1
  have hneg (z : Point m n) : vector q (-z) = -vector q z := by
    ext (i | j) <;> simp [vector, numerator, neg_div]
  have hclosed (z) (hz' : z ∈ S) : -z ∈ S := by
    obtain ⟨he, hs⟩ := (mem_candidates hR z).mp hz'
    apply (mem_candidates hR (-z)).mpr
    constructor
    · have : reduce q (-z).1 = -reduce q z.1 := by ext i; simp [reduce]
      simpa [this] using he
    · simpa [hneg] using hs
  have h0 : 0 ∉ S := fun h ↦ hz 0 h (by ext; simp [reduce])
  have hc := (dual_counts S hz).2.2 hclosed h0
  rw [card_univ] at hc
  have hreal : 2 * ((designs (fun A ↦ (members (dual (q := q)) S A).Nonempty)).card : ℝ) *
      (q : ℝ)^n ≤ S.card * (Fintype.card (Design m n q) : ℝ) := by exact_mod_cast hc
  simp only [probability, rawExit_iff hR h1]
  have htot : (0 : ℝ) < Fintype.card (Design m n q) := by exact_mod_cast Fintype.card_pos
  change _ / _ ≤ (S.card : ℝ) / 2 / _
  rw [div_le_div_iff₀ htot (pow_pos prime_pos _)]
  linarith

/-- Part 172, Proposition 2 for a single index. The two factors of two cancel. -/
theorem rawExit_probability {R : ℝ} (h1 : R ≤ 1) :
    probability (fun A : Design m n q ↦ rawExit A R) ≤
      inwardVolume (Coord m n) (q * R) / (q : ℝ)^n := by
  by_cases hR : 0 ≤ R
  swap
  · have noExit (A : Design m n q) : ¬rawExit A R := by
      rintro ⟨x, _, _, hs⟩
      exact hR ((norm_nonneg _).trans hs.le)
    simp only [probability, designs, noExit, filter_false, card_empty, Nat.cast_zero, zero_div]
    unfold inwardVolume
    positivity
  let T := SigabaNeo.Planted.integerBall (ι := Coord m n) (q * R)
  have hc : (candidates m n q R).card ≤ T.card := by
    exact (card_filter_le _ _).trans_eq (card_map _)
  have hv := inward_half_cube T (q * R) (fun z hz ↦
    ((SigabaNeo.Planted.mem_integerBall (mul_nonneg prime_pos.le hR) z).mp hz).2)
  apply (probability_le_candidates hR h1).trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg prime_pos.le _)
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by norm_num)).trans hv

/-- Restriction to the first `n` columns of the single design drawn for the entire pass. -/
def designPrefix {K : ℕ} (h : n ≤ K) (A : Design m K q) : Design m n q :=
  fun i j ↦ A i (j.castLE h)

/-- Every prefix of one uniform design is uniform, by equal cardinality of its fibers. -/
theorem prefix_probability {K : ℕ} (h : n ≤ K) (P : Design m n q → Prop) :
    probability (fun A ↦ P (designPrefix h A)) = probability P := by
  let f : Design m K q →+ Design m n q := ⟨⟨designPrefix h, rfl⟩, fun _ _ ↦ rfl⟩
  have onto : Function.Surjective f := by
    intro B
    refine ⟨fun i j ↦ if hj : j.val < n then B i ⟨j.val, hj⟩ else 0, ?_⟩
    ext i j
    change (if hj : j.val < n then _ else _) = _
    simp [j.isLt]
  let c := (univ.filter fun A ↦ f A = 0).card
  have fibers (B : Design m n q) : (univ.filter fun A ↦ f A = B).card = c := by
    dsimp only [c]
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective onto _ _)
  have count (T : Finset (Design m n q)) :
      (univ.filter fun A ↦ f A ∈ T).card = T.card * c := by
    rw [← sum_card_fiberwise_eq_card_filter]
    simp [fibers]
  have total : Fintype.card (Design m K q) = Fintype.card (Design m n q) * c := by
    simpa using count univ
  have event : (designs (fun A ↦ P (designPrefix h A))).card = (designs P).card * c := by
    convert count (designs P) using 1
    congr 1
    ext A
    simp [designs, f]
    rfl
  rw [probability, probability, event, total, Nat.cast_mul, Nat.cast_mul]
  have htot := Fintype.card_pos (α := Design m K q)
  rw [total] at htot
  exact mul_div_mul_right _ _ (by exact_mod_cast (Nat.pos_of_mul_pos_left htot).ne')

/-- Union over any finite family of prefixes, with arbitrary overlaps on the same design. -/
theorem pass_probability {T K : ℕ} (cols : Fin T → ℕ) (len : ∀ t, cols t ≤ K)
    (R : Fin T → ℝ) (h1 : ∀ t, R t ≤ 1) :
    probability (fun A : Design m K q ↦ ∃ t, rawExit (designPrefix (len t) A) (R t)) ≤
      ∑ t, inwardVolume (Coord m (cols t)) (q * R t) / (q : ℝ)^(cols t) := by
  let E (t : Fin T) := designs (fun A : Design m K q ↦ rawExit (designPrefix (len t) A) (R t))
  have eqUnion : designs (fun A : Design m K q ↦ ∃ t, rawExit (designPrefix (len t) A) (R t)) =
      univ.biUnion E := by ext; simp [E, designs]
  calc
    _ ≤ ∑ t, probability (fun A : Design m K q ↦ rawExit (designPrefix (len t) A) (R t)) := by
      simp only [probability, eqUnion, ← sum_div, ← Nat.cast_sum]
      exact div_le_div_of_nonneg_right (by exact_mod_cast card_biUnion_le) (by positivity)
    _ ≤ _ := sum_le_sum fun t _ ↦ by
      rw [prefix_probability (len t) (fun B : Design m (cols t) q ↦ rawExit B (R t))]
      exact rawExit_probability (h1 t)

/-- The retained frame at a given prefix, for any subspace chosen by the reducer. -/
def sectionFrame (A : Design m n q) (S : Submodule ℝ (Space m n)) : MarkedFrame (Fin m) q where
  space := S
  lattice := projectedModule (rawGraph A) S
  mark i := S.orthogonalProjectionOnto (EuclideanSpace.basisFun _ ℝ (.inl i))
  multiple := graph_mark_multiple _ _ _ _

omit [Fact q.Prime] in
/-- On the good event, the index-specific floor holds on every section and persists along
every subsequent marked history starting from it. -/
theorem good_prefix_floor (A : Design m n q) {R : ℝ} (h1 : R ≤ 1) (good : ¬rawExit A R)
    (S : Submodule ℝ (Space m n)) {F : MarkedFrame (Fin m) q}
    (path : MarkedHistory (sectionFrame A S) F) (x : F.Dual) (hx : x ≠ 0) : R ≤ ‖x.val‖ := by
  by_contra! hs
  obtain ⟨⟨y, ts⟩, hy, _⟩ := path.existsUnique_lineage x
  obtain ⟨hy0, hnorm⟩ := path.lineage_short_restart x y ts hy hx (hs.trans_le h1)
  have hm := y.property
  change y.val ∈ metricDual (projectedModule (rawGraph A) S) at hm
  rw [metricDual_projectedModule] at hm
  apply good
  exact ⟨y.val.val, hm, fun e ↦ hy0 (Subtype.ext (Subtype.ext e)), hnorm.trans_lt hs⟩

end SigabaNeo.Wall1.DualExit

#print axioms SigabaNeo.Wall1.DualExit.rawExit_iff
#print axioms SigabaNeo.Wall1.DualExit.signed_first_moment
#print axioms SigabaNeo.Wall1.DualExit.probability_le_candidates
#print axioms SigabaNeo.Wall1.DualExit.rawExit_probability
#print axioms SigabaNeo.Wall1.DualExit.prefix_probability
#print axioms SigabaNeo.Wall1.DualExit.pass_probability
#print axioms SigabaNeo.Wall1.DualExit.good_prefix_floor
