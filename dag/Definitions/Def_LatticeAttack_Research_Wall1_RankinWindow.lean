import Definitions.Def_LatticeAttack_Research_Wall1_ProjectedCovolume

set_option autoImplicit true

/-! # Rankin minima of an appended and projected window -/

noncomputable section
namespace SigabaNeo.Wall1

open Submodule WithLp
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Independent lattice tuples parameterize all sublattices of the specified rank.
The empty infimum is infinity, including ranks exceeding the ambient dimension. -/
structure RankinFamily (L : Submodule ℤ V) (i : ℕ) where
  vec : Fin i → V
  mem : ∀ j, vec j ∈ L
  ind : LinearIndependent ℝ vec

def familyVolume {i : ℕ} (b : Fin i → V) : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ b).det)

def rankinMinimum (L : Submodule ℤ V) (i : ℕ) : ℝ≥0∞ :=
  ⨅ b : RankinFamily L i, familyVolume b.vec

@[simp] theorem rankinMinimum_zero (L : Submodule ℤ V) : rankinMinimum L 0 = 1 := by
  let b : RankinFamily L 0 := ⟨Fin.elim0, fun i ↦ i.elim0, linearIndependent_empty_type⟩
  have : Nonempty (RankinFamily L 0) := ⟨b⟩
  simp [rankinMinimum, familyVolume, Matrix.det_isEmpty]

/-- Every independent family in the projection lifts, together with the selected head, to a
family in the window. This gives the retained Rankin inequality for every nonzero head. -/
theorem rankin_project [FiniteDimensional ℝ V] (L : Submodule ℤ V) (i : ℕ)
    {v : V} (hv : v ∈ L) (hv0 : v ≠ 0) :
    rankinMinimum L (i + 1) / ENNReal.ofReal ‖v‖ ≤
      rankinMinimum (projectedModule L (ℝ ∙ v)ᗮ) i := by
  apply le_iInf
  intro b
  choose w hw he using b.mem
  let f := Fin.cons (α := fun _ ↦ V) v w
  have hG : (Matrix.gram ℝ f).det = ‖v‖ ^ 2 * (Matrix.gram ℝ b.vec).det := by
    rw [det_gram_project_tail]
    simp only [f, Fin.cons_zero, Fin.cons_succ]
    congr 2
    ext j k
    exact congrArg₂ (inner ℝ) (congrArg Subtype.val (he j)) (congrArg Subtype.val (he k))
  have hbpos := (Matrix.posDef_gram_of_linearIndependent b.ind).det_pos
  let F : RankinFamily L (i + 1) :=
    ⟨f, Fin.forall_fin_succ.mpr ⟨hv, hw⟩,
      Matrix.det_gram_ne_zero_iff_linearIndependent.mp (hG ▸ (mul_pos
        (sq_pos_of_pos (norm_pos_iff.mpr hv0)) hbpos).ne')⟩
  have hh := iInf_le (fun t : RankinFamily L (i + 1) ↦ familyVolume t.vec) F
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr hv0))
    ENNReal.ofReal_ne_top).2
  apply hh.trans_eq
  change ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ f).det) = _
  rw [hG, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
  rfl

private theorem window_coordinates (L : Submodule ℤ V) (u : V) {w : WindowSpace V}
    (hw : w ∈ appendWindow L u) :
    ∃ l ∈ L, ∃ j : ℤ, w = horizontalInclusion l + j • toLp 2 (u, (1 : ℝ)) := by
  obtain ⟨_, ⟨l, hl, rfl⟩, _, hz, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨j, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨l, hl, j, rfl⟩

private theorem window_height (L : Submodule ℤ V) (u : V) {w : WindowSpace V}
    (hw : w ∈ appendWindow L u) : (⌊w.snd⌋ : ℝ) = w.snd := by
  obtain ⟨_, _, j, rfl⟩ := window_coordinates L u hw
  simp [horizontalInclusion, zsmul_eq_mul]

private theorem fst_mem_of_height_zero (L : Submodule ℤ V) (u : V) {w : WindowSpace V}
    (hw : w ∈ appendWindow L u) (hz : w.snd = 0) : w.fst ∈ L := by
  obtain ⟨l, hl, j, rfl⟩ := window_coordinates L u hw
  have hj : j = 0 := by simpa [horizontalInclusion, zsmul_eq_mul] using hz
  simpa [hj, horizontalInclusion] using hl

private theorem horizontal_gram {n : ℕ} (b : Fin n → V) :
    Matrix.gram ℝ (horizontalInclusion ∘ b) = Matrix.gram ℝ b := by
  ext i j
  change ⟪b i, b j⟫ + (0 : ℝ) * 0 = _
  simp [Matrix.gram_apply]

private theorem gram_add_row {n : ℕ} (b : Fin n → V) {i j : Fin n} (hij : i ≠ j) (c : ℤ) :
    (Matrix.gram ℝ (Function.update b i (b i + c • b j))).det = (Matrix.gram ℝ b).det := by
  let A := Matrix.gram ℝ b
  let B := A.updateRow i (A i + (c : ℝ) • A j)
  let b' := Function.update b i (b i + c • b j)
  have hB (k m) : B k m = ⟪b' k, b m⟫ := by
    by_cases h : k = i
    · subst k
      simp [B, b', A, Matrix.gram_apply, inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left]
    · simp [B, b', A, Matrix.updateRow_ne h, Function.update_of_ne h, Matrix.gram_apply]
  have hC : Matrix.gram ℝ b' = B.updateCol i (fun k ↦ B k i + (c : ℝ) • B k j) := by
    ext k m
    by_cases h : m = i
    · subst m
      simp only [Matrix.gram_apply, Matrix.updateCol_self, hB, smul_eq_mul]
      conv_lhs => rw [show b' i = b i + c • b j from Function.update_self ..]
      simp [inner_add_right, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
    · rw [Matrix.updateCol_ne h, Matrix.gram_apply, hB, show b' m = b m from
        Function.update_of_ne h ..]
  change (Matrix.gram ℝ b').det = _
  rw [hC, Matrix.det_updateCol_add_smul_self _ hij, Matrix.det_updateRow_add_smul_self _ hij]

/-- Integral row operations put all vertical height in at most one row while preserving
the Gram determinant. Minimize the sum of absolute heights and use Euclidean division. -/
private theorem adapted_family (L : Submodule ℤ V) (u : V) {n : ℕ}
    (b : RankinFamily (appendWindow L u) (n + 1)) :
    ∃ c : RankinFamily (appendWindow L u) (n + 1),
      familyVolume c.vec = familyVolume b.vec ∧ ∀ j : Fin n, (c.vec j.succ).snd = 0 := by
  classical
  let W := appendWindow L u
  let cost (f : Fin (n + 1) → WindowSpace V) := ∑ i, (⌊(f i).snd⌋).natAbs
  let P (N : ℕ) := ∃ f : RankinFamily W (n + 1),
    familyVolume f.vec = familyVolume b.vec ∧ cost f.vec = N
  have hex : ∃ N, P N := ⟨_, b, rfl, rfl⟩
  obtain ⟨f, hf, hmin⟩ := Nat.find_spec hex
  let z (i : Fin (n + 1)) := ⌊(f.vec i).snd⌋
  have hz (i) : (z i : ℝ) = (f.vec i).snd := window_height L u (f.mem i)
  have reduce (i j : Fin (n + 1)) (hij : i ≠ j) (hj : z j ≠ 0) (hle : (z j).natAbs ≤ (z i).natAbs) :
      False := by
    let d := -(z i / z j)
    let g := Function.update f.vec i (f.vec i + d • f.vec j)
    have hdet := gram_add_row f.vec hij d
    let G : RankinFamily W (n + 1) := ⟨g, fun k ↦ by
      by_cases hk : k = i
      · subst k; simpa [g] using W.add_mem (f.mem i) (W.smul_mem d (f.mem j))
      · simpa [g, Function.update_of_ne hk] using f.mem k,
      Matrix.det_gram_ne_zero_iff_linearIndependent.mp
        (hdet ▸ Matrix.det_gram_ne_zero_iff_linearIndependent.mpr f.ind)⟩
    have hvol : familyVolume G.vec = familyVolume b.vec := by
      change ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ g).det) = _
      rw [hdet]; exact hf
    have hheight : (g i).snd = ((z i % z j : ℤ) : ℝ) := by
      rw [Int.emod_def]
      simp [g, d, zsmul_eq_mul, ← hz, mul_comm, sub_eq_add_neg]
    have hlt : (z i % z j).natAbs < (z i).natAbs := by
      have h1 := Int.emod_lt_abs (z i) hj
      have h2 := Int.emod_nonneg (z i) hj
      have h3 : (z i % z j).natAbs < (z j).natAbs := by
        rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonneg h2]
        exact h1
      exact h3.trans_le hle
    have hc : cost g < cost f.vec := by
      apply Finset.sum_lt_sum
      · intro k _
        by_cases hk : k = i
        · subst k; simpa [hheight] using hlt.le
        · simp [g, Function.update_of_ne hk]
      · exact ⟨i, Finset.mem_univ _, by simpa [hheight] using hlt⟩
    exact (not_lt_of_ge (Nat.find_min' hex ⟨G, hvol, rfl⟩)) (hc.trans_eq hmin)
  by_cases hall : ∀ i, z i = 0
  · exact ⟨f, hf, fun j ↦ by rw [← hz, hall]; simp⟩
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  let e := Equiv.swap (0 : Fin (n + 1)) i
  let c : RankinFamily W (n + 1) := ⟨f.vec ∘ e, fun j ↦ f.mem _, f.ind.comp _ e.injective⟩
  have hvol : familyVolume c.vec = familyVolume f.vec := by
    unfold familyVolume
    rw [show Matrix.gram ℝ c.vec = (Matrix.gram ℝ f.vec).submatrix e e by rfl,
      Matrix.det_submatrix_equiv_self]
  refine ⟨c, hvol.trans hf, fun j ↦ ?_⟩
  have hne : e j.succ ≠ i := by
    rw [← show e 0 = i from Equiv.swap_apply_left ..]
    exact e.injective.ne (Fin.succ_ne_zero _)
  change (f.vec (e j.succ)).snd = 0
  rw [← hz, Int.cast_eq_zero]
  by_contra hj
  rcases le_total (z i).natAbs (z (e j.succ)).natAbs with h | h
  · exact reduce _ _ hne hi h
  · exact reduce _ _ hne.symm hj h

private theorem horiz_of_zero {x : WindowSpace V} (hx : x.snd = 0) :
    horizontalInclusion x.fst = x :=
  (WithLp.equiv 2 (V × ℝ)).injective (Prod.ext rfl hx.symm)

private theorem horizontal_span {n : ℕ} (b : Fin n → V) :
    span ℝ (Set.range (horizontalInclusion ∘ b)) =
      (span ℝ (Set.range b)).map horizontalInclusion := by rw [Set.range_comp, map_span]

private theorem projected_vertical_height {n : ℕ} (b : Fin n → V) (w : WindowSpace V) :
    (prefixProjection (horizontalInclusion ∘ b) w).snd = w.snd := by
  let K := span ℝ (Set.range (horizontalInclusion ∘ b))
  change (Kᗮ.starProjection w).snd = _
  rw [starProjection_orthogonal_val, sub_snd]
  have hmem : K.starProjection w ∈ (span ℝ (Set.range b)).map horizontalInclusion :=
    (horizontal_span b).le (K.starProjection_apply_mem w)
  obtain ⟨_, _, he⟩ := hmem
  rw [← he]
  exact sub_zero _

/-- The vertical minimum after projecting away from an old horizontal family. -/
def verticalMinimum (L : Submodule ℤ V) (u : V) {n : ℕ} (b : Fin n → V) : ℝ≥0∞ :=
  ⨅ w : {w : appendWindow L u // w.val.snd ≠ 0},
    ENNReal.ofReal ‖prefixProjection (horizontalInclusion ∘ b) w.val.val‖

theorem one_le_verticalMinimum (L : Submodule ℤ V) (u : V) {n : ℕ} (b : Fin n → V) :
    1 ≤ verticalMinimum L u b := by
  apply le_iInf
  intro w
  have h := window_height L u w.val.property
  have hn : ⌊w.val.val.snd⌋ ≠ 0 := by intro he; rw [he, Int.cast_zero] at h; exact w.2 h.symm
  have hbase : (1 : ℝ) ≤ |(⌊w.val.val.snd⌋ : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  rw [h, ← Real.norm_eq_abs, ← projected_vertical_height b w.val.val] at hbase
  exact_mod_cast ENNReal.ofReal_le_ofReal (hbase.trans (WithLp.norm_snd_le _ _))

private theorem cons_volume [FiniteDimensional ℝ V] {n : ℕ} (b : Fin n → V) (w : WindowSpace V) :
    familyVolume (Fin.cons (α := fun _ ↦ WindowSpace V) w (horizontalInclusion ∘ b)) =
      familyVolume b * ENNReal.ofReal ‖prefixProjection (horizontalInclusion ∘ b) w‖ := by
  let h := horizontalInclusion ∘ b
  let f := Fin.cons (α := fun _ ↦ WindowSpace V) w h
  have hd := det_gram_project_tail f
  simp only [f, Fin.cons_zero, Fin.cons_succ] at hd
  have he := hd.trans (gram_project_exchange h w)
  rw [horizontal_gram] at he
  unfold familyVolume
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    ENNReal.ofReal_mul (norm_nonneg _), mul_comm]

private def horizontalFamily {L : Submodule ℤ V} (u : V) {n : ℕ} (b : RankinFamily L n) :
    RankinFamily (appendWindow L u) n where
  vec := horizontalInclusion ∘ b.vec
  mem j := mem_sup_left ⟨_, b.mem j, rfl⟩
  ind := Matrix.det_gram_ne_zero_iff_linearIndependent.mp
    ((congrArg Matrix.det (horizontal_gram b.vec)) ▸
      Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.ind)

private def verticalFamily {L : Submodule ℤ V} (u : V) {n : ℕ} (b : RankinFamily L n)
    (w : {w : appendWindow L u // w.val.snd ≠ 0}) : RankinFamily (appendWindow L u) (n + 1) where
  vec := Fin.cons (α := fun _ ↦ WindowSpace V) w.val.val (horizontalInclusion ∘ b.vec)
  mem := Fin.forall_fin_succ.mpr ⟨w.val.property, (horizontalFamily u b).mem⟩
  ind := linearIndependent_finCons.mpr ⟨(horizontalFamily u b).ind, by
    rw [horizontal_span]
    rintro ⟨y, _, he⟩
    exact w.property (congrArg WithLp.snd he).symm⟩

/-- Exact Rankin recursion, indexing the horizontal intersection by arbitrary independent
integer bases. Saturated and nonsaturated sublattices are both allowed in the infimum. -/
theorem rankin_append [FiniteDimensional ℝ V] (L : Submodule ℤ V) (u : V) (n : ℕ) :
    rankinMinimum (appendWindow L u) (n + 1) =
      min (rankinMinimum L (n + 1))
        (⨅ b : RankinFamily L n, familyVolume b.vec * verticalMinimum L u b.vec) := by
  let W := appendWindow L u
  apply le_antisymm
  · apply le_min
    · apply le_iInf
      intro b
      apply (iInf_le (fun c : RankinFamily W (n+1) ↦ familyVolume c.vec)
        (horizontalFamily u b)).trans_eq
      exact congrArg (fun M ↦ ENNReal.ofReal (Real.sqrt (Matrix.det M))) (horizontal_gram _)
    · apply le_iInf
      intro b
      have hp : familyVolume b.vec ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
        (Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent b.ind).det_pos)
      rw [verticalMinimum, ENNReal.mul_iInf_of_ne hp ENNReal.ofReal_ne_top]
      apply le_iInf
      intro w
      exact (iInf_le (fun c : RankinFamily W (n+1) ↦ familyVolume c.vec)
        (verticalFamily u b w)).trans_eq (cons_volume b.vec _)
  · apply le_iInf
    intro b
    obtain ⟨c, hc, hz⟩ := adapted_family L u b
    rw [← hc]
    by_cases hzero : (c.vec 0).snd = 0
    · have h0 : ∀ j, (c.vec j).snd = 0 := Fin.forall_fin_succ.mpr ⟨hzero, hz⟩
      let f := fun j ↦ (c.vec j).fst
      have he : horizontalInclusion ∘ f = c.vec := funext fun j ↦ horiz_of_zero (h0 j)
      have hg : Matrix.gram ℝ c.vec = Matrix.gram ℝ f := he ▸ horizontal_gram f
      let F : RankinFamily L (n+1) := ⟨f, fun j ↦ fst_mem_of_height_zero L u (c.mem j) (h0 j),
        Matrix.det_gram_ne_zero_iff_linearIndependent.mp ((congrArg Matrix.det hg) ▸
          Matrix.det_gram_ne_zero_iff_linearIndependent.mpr c.ind)⟩
      apply (min_le_left _ _).trans ((iInf_le (fun t ↦ familyVolume (RankinFamily.vec t)) F).trans_eq ?_)
      exact congrArg (fun M ↦ ENNReal.ofReal (Real.sqrt (Matrix.det M))) hg.symm
    · let f := fun j : Fin n ↦ (c.vec j.succ).fst
      have he : horizontalInclusion ∘ f = c.vec ∘ Fin.succ := funext fun j ↦ horiz_of_zero (hz j)
      have hi : LinearIndependent ℝ (horizontalInclusion ∘ f) := he.symm ▸ c.ind.comp _ (Fin.succ_injective n)
      let F : RankinFamily L n := ⟨f, fun j ↦ fst_mem_of_height_zero L u (c.mem _) (hz j),
        hi.of_comp horizontalInclusion⟩
      let w : {w : appendWindow L u // w.val.snd ≠ 0} := ⟨⟨_, c.mem 0⟩, hzero⟩
      have hcons : Fin.cons (α := fun _ ↦ WindowSpace V) w.val.val (horizontalInclusion ∘ f) =
          c.vec := by rw [he]; exact Fin.cons_self_tail _
      refine (min_le_right _ _).trans ((iInf_le (fun t : RankinFamily L n ↦
        familyVolume t.vec * verticalMinimum L u t.vec) F).trans ?_)
      calc
        _ ≤ familyVolume f * ENNReal.ofReal ‖prefixProjection (horizontalInclusion ∘ f) w.val.val‖ :=
          mul_le_mul_right (iInf_le _ w) _
        _ = _ := (cons_volume f w.val.val).symm.trans (congrArg familyVolume hcons)

/-- The pathwise Rankin bound after one append and projection. -/
theorem rankin_retained [FiniteDimensional ℝ V] (L : Submodule ℤ V) (u : V) (n : ℕ)
    {v : WindowSpace V} (hv : v ∈ appendWindow L u) (hv0 : v ≠ 0) :
    min (rankinMinimum L n) (rankinMinimum L (n+1)) / ENNReal.ofReal ‖v‖ ≤
      rankinMinimum (retainedWindow L u v) n := by
  apply le_trans _ (rankin_project _ n hv hv0)
  apply ENNReal.div_le_div_right
  rw [rankin_append]
  apply le_min (min_le_right _ _)
  refine (min_le_left _ _).trans (le_iInf fun b ↦ ?_)
  apply (iInf_le (fun c : RankinFamily L n ↦ familyVolume c.vec) b).trans
  simpa only [mul_one] using mul_le_mul_right (one_le_verticalMinimum L u b.vec) (familyVolume b.vec)

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.rankinMinimum_zero
#print axioms SigabaNeo.Wall1.rankin_project
#print axioms SigabaNeo.Wall1.one_le_verticalMinimum
#print axioms SigabaNeo.Wall1.rankin_append
#print axioms SigabaNeo.Wall1.rankin_retained
