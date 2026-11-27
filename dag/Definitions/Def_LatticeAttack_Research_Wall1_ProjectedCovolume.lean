import Definitions.Def_LatticeAttack_Research_Wall1_VerticalRefinement
import Definitions.Def_LatticeAttack_Research_Wall1_RetainedCovolume

set_option autoImplicit true

/-! # Intrinsic covolume of the retained window -/

noncomputable section

namespace SigabaNeo.Wall1

open Submodule Module MeasureTheory WithLp ZSpan
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Interchanging the order of the head and tail gives the two base-times-height
formulas for the same parallelepiped, including rank-deficient families. -/
theorem gram_project_exchange {n : ℕ} (b : Fin n → V) (v : V) :
    ‖v‖ ^ 2 * (Matrix.gram ℝ (fun i ↦ (ℝ ∙ v)ᗮ.starProjection (b i))).det =
      ‖prefixProjection b v‖ ^ 2 * (Matrix.gram ℝ b).det := by
  let f := Fin.cons (α := fun _ ↦ V) v b
  have h := det_gram_project_tail f
  simp only [f, Fin.cons_zero, Fin.cons_succ] at h
  rw [← h, projectedLength_sq_mul_det, Fin.snoc_eq_cons_rotate]
  exact (Matrix.det_submatrix_equiv_self (finRotate _) (Matrix.gram ℝ f)).symm

/-- The squared covolume in the induced Euclidean volume is the Gram determinant. -/
theorem covolume_span_sq_eq_gram [MeasurableSpace V] [BorelSpace V] {n : ℕ}
    (b : Basis (Fin n) ℝ V) :
    ZLattice.covolume (span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  let e := (stdOrthonormalBasis ℝ V).reindex (finCongr ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin n)))
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume (b.restrictScalars ℤ) e.toBasis,
    measureReal_congr (fundamentalDomain_ae_parallelepiped e.toBasis volume)]
  have vol : volume.real (parallelepiped e.toBasis) = 1 := by
    simpa [Measure.real] using congrArg ENNReal.toReal e.volume_parallelepiped
  have hb : Subtype.val ∘ (b.restrictScalars ℤ) = (b : Fin n → V) := by
    funext i
    exact b.restrictScalars_apply ℤ i
  rw [vol, mul_one, hb, sq_abs, Matrix.gram_eq_conjTranspose_mul e, Matrix.det_mul,
    Matrix.det_conjTranspose, star_trivial, sq]
  congr 1

omit [FiniteDimensional ℝ V] in
/-- The squared intrinsic covolume factor for any horizontal family. For an independent
family the two Gram determinants are the squared covolumes in their respective spans.
This form also covers winners with zero horizontal component. -/
theorem winnerCompression_gram {n : ℕ} (b : Fin n → V) (v : WindowSpace V) (hv : 0 < v.snd) :
    (Matrix.gram ℝ (winnerCompression v ∘ b)).det = (Matrix.gram ℝ b).det *
      (1 - ‖(span ℝ (Set.range b)).starProjection v.fst‖ ^ 2 / ‖v‖ ^ 2) := by
  let K := span ℝ (Set.range b)
  let h := horizontalInclusion ∘ b
  let S := span ℝ (Set.range h)
  have hS : S = K.map horizontalInclusion := by
    change span ℝ (Set.range (horizontalInclusion ∘ b)) = _
    rw [Set.range_comp, map_span]
  have hh (x y : V) : ⟪horizontalInclusion x, horizontalInclusion y⟫ = ⟪x, y⟫ := by
    change ⟪x, y⟫ + (0 : ℝ) * 0 = _
    simp
  have hP : S.starProjection v = horizontalInclusion (K.starProjection v.fst) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hS]
      exact ⟨_, K.starProjection_apply_mem _, rfl⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hS.le hz
      change ⟪v.fst - K.starProjection v.fst, y⟫ + 0 * _ = 0
      simpa using (Submodule.mem_orthogonal' K _).mp (K.sub_starProjection_mem_orthogonal v.fst) y hy
  have hg : Matrix.gram ℝ h = Matrix.gram ℝ b := by ext i j; exact hh _ _
  have hc : Matrix.gram ℝ (fun i ↦ (ℝ ∙ v)ᗮ.starProjection (h i)) =
      Matrix.gram ℝ (winnerCompression v ∘ b) := by
    ext i j
    rw [Matrix.gram_apply, ← (winnerStraightening v).inner_map_map, Matrix.gram_apply]
    change ⟪winnerStraightening v ((ℝ ∙ v)ᗮ.starProjection (horizontalInclusion (b i))),
      winnerStraightening v ((ℝ ∙ v)ᗮ.starProjection (horizontalInclusion (b j)))⟫ = _
    rw [straighten_project_horizontal v hv, straighten_project_horizontal v hv, hh]
    rfl
  have he := gram_project_exchange h v
  rw [hg, hc] at he
  have hp := norm_sq_eq_add_norm_sq_starProjection v S
  rw [hP, show ‖horizontalInclusion (K.starProjection v.fst)‖ = ‖K.starProjection v.fst‖ from
    WithLp.norm_toLp_fst 2 V ℝ _] at hp
  change ‖v‖ ^ 2 = ‖K.starProjection v.fst‖ ^ 2 + ‖prefixProjection h v‖ ^ 2 at hp
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr (by rintro rfl; exact (lt_irrefl 0) hv)
  change _ = _ * (1 - ‖K.starProjection v.fst‖ ^ 2 / ‖v‖ ^ 2)
  field_simp [hn]
  linear_combination he - (Matrix.gram ℝ b).det * hp

private abbrev projectHoriz (v : WindowSpace V) : V →ₗ[ℝ] (ℝ ∙ v)ᗮ :=
  (ℝ ∙ v)ᗮ.orthogonalProjectionOnto.toLinearMap.comp horizontalInclusion

omit [FiniteDimensional ℝ V] in
private theorem gram_project_horizontal {n : ℕ} (b : Basis (Fin n) ℝ V) (v : WindowSpace V) :
    ‖v‖ ^ 2 * (Matrix.gram ℝ (fun i ↦ projectHoriz v (b i))).det =
      v.snd ^ 2 * (Matrix.gram ℝ b).det := by
  let f := fun i ↦ horizontalInclusion (b i)
  let S := span ℝ (Set.range f)
  have hS : S = horizontalInclusion.range := by
    change span ℝ (Set.range (horizontalInclusion ∘ ⇑b)) = _
    rw [Set.range_comp, ← map_span, b.span_eq, Submodule.map_top]
  let p : WindowSpace V := toLp 2 (0, v.snd)
  have hp : p ∈ Sᗮ := by
    rw [hS]
    rintro _ ⟨y, rfl⟩
    change ⟪y, (0 : V)⟫ + _ * 0 = 0
    simp
  have hdiff : horizontalInclusion v.fst ∈ S := hS ▸ ⟨_, rfl⟩
  have hdecomp : v = horizontalInclusion v.fst + p := by
    exact (WithLp.equiv 2 (V × ℝ)).injective (Prod.ext (add_zero _).symm (zero_add _).symm)
  have hvp : prefixProjection f v = p := by
    change Sᗮ.starProjection v = p
    conv_lhs => rw [hdecomp, map_add]
    rw [Submodule.starProjection_orthogonal_apply_eq_zero hdiff, zero_add, Sᗮ.starProjection_eq_self_iff.mpr hp]
  have hm : Matrix.gram ℝ f = Matrix.gram ℝ b := by
    ext i j
    change ⟪b i, b j⟫ + (0 : ℝ) * 0 = _
    simp [Matrix.gram_apply]
  have h := gram_project_exchange f v
  rw [hvp, hm, show ‖p‖ = ‖v.snd‖ from WithLp.norm_toLp_snd 2 V ℝ _, Real.norm_eq_abs,
    sq_abs] at h
  exact h

private theorem retained_eq_project_refinement (L : Submodule ℤ V) (u l : V)
    (k : ℕ) (hk : 0 < k) (v : WindowSpace V)
    (hv : v = horizontalInclusion l + (k : ℝ) • toLp 2 (u, (1 : ℝ))) :
    retainedWindow L u v = (L ⊔ ℤ ∙ ((k : ℝ)⁻¹ • l)).map ((projectHoriz v).restrictScalars ℤ) := by
  let P := (ℝ ∙ v)ᗮ.orthogonalProjectionOnto.toLinearMap
  have hkill : P v = 0 := Subtype.ext (starProjection_orthogonalComplement_singleton_eq_zero v)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hgen : P (toLp 2 (u, (1 : ℝ))) = -projectHoriz v ((k : ℝ)⁻¹ • l) := by
    have h := congrArg P hv
    rw [hkill, map_add, map_smul] at h
    have he := eq_neg_of_add_eq_zero_right h.symm
    change (k : ℝ) • P (toLp 2 (u, (1 : ℝ))) = -projectHoriz v l at he
    rw [map_smul, ← smul_neg, ← he, inv_smul_smul₀ hkR]
  change (appendWindow L u).map (P.restrictScalars ℤ) = _
  rw [appendWindow, Submodule.map_sup, ← Submodule.map_comp, Submodule.map_sup, map_span, map_span, Set.image_singleton,
    Set.image_singleton]
  change _ ⊔ ℤ ∙ P (toLp 2 (u, (1 : ℝ))) = _ ⊔ _
  rw [hgen]
  congr 1
  apply le_antisymm <;> rw [span_singleton_le_iff_mem]
  · exact (ℤ ∙ _).neg_mem (mem_span_singleton_self _)
  · simpa using (ℤ ∙ -projectHoriz v ((k : ℝ)⁻¹ • l)).neg_mem (mem_span_singleton_self _)

/-- A projection of a full horizontal lattice into the complement of a positive-height
vector multiplies its intrinsic covolume by height divided by length. -/
theorem covolume_project_horizontal [MeasurableSpace V] [BorelSpace V]
    (R : Submodule ℤ V) [DiscreteTopology R] [IsZLattice ℝ R]
    (v : WindowSpace V) (hv : 0 < v.snd) :
    ZLattice.covolume (R.map ((projectHoriz v).restrictScalars ℤ)) =
      v.snd / ‖v‖ * ZLattice.covolume R := by
  let b := (Module.finBasis ℤ R).ofZLatticeBasis ℝ R
  have hv0 : v ≠ 0 := by rintro rfl; exact (lt_irrefl 0) hv
  have hs := norm_pos_iff.mpr hv0
  let f := fun i ↦ projectHoriz v (b i)
  have he := gram_project_horizontal b v
  have hpos := (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos
  have hin : LinearIndependent ℝ f := (Matrix.det_gram_ne_zero_iff_linearIndependent).1 (by
    intro hz
    change (Matrix.gram ℝ f).det = 0 at hz
    change ‖v‖ ^ 2 * (Matrix.gram ℝ f).det = _ at he
    rw [hz, mul_zero] at he
    exact (mul_pos (sq_pos_of_pos hv) hpos).ne' he.symm)
  have hdim := (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hv0, (WithLp.linearEquiv 2 ℝ (V × ℝ)).finrank_eq,
    Module.finrank_prod, Module.finrank_self] at hdim
  let c := basisOfLinearIndependentOfCardEqFinrank' f hin
    (by rw [← Module.finrank_eq_card_basis b]; omega)
  have hc : ⇑c = f := Basis.coe_mk ..
  have hR := (Module.finBasis ℤ R).ofZLatticeBasis_span ℝ
  have himg : R.map ((projectHoriz v).restrictScalars ℤ) = span ℤ (Set.range c) := by
    rw [hc]
    conv_lhs => rw [← hR, map_span, ← Set.range_comp]
    rfl
  have hcvol := covolume_span_sq_eq_gram c
  have hbvol := covolume_span_sq_eq_gram b
  rw [← himg] at hcvol
  rw [hc] at hcvol
  rw [hR] at hbvol
  apply (mul_right_cancel₀ hs.ne')
  rw [mul_right_comm, div_mul_cancel₀ _ hs.ne']
  apply (sq_eq_sq₀ (mul_nonneg ENNReal.toReal_nonneg hs.le)
    (mul_nonneg hv.le ENNReal.toReal_nonneg)).mp
  change (ZLattice.covolume (R.map ((projectHoriz v).restrictScalars ℤ)) * ‖v‖) ^ 2 =
    (v.snd * ZLattice.covolume R) ^ 2
  rw [mul_pow, mul_pow, hcvol, hbvol, mul_comm]
  exact he

/-- Exact intrinsic Euclidean covolume of the new retained lattice. -/
theorem verticalWinner_covolume [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (u l : V) (hl : l ∈ L)
    (k : ℕ) (hk : 0 < k) (v : WindowSpace V)
    (hv : v = horizontalInclusion l + (k : ℝ) • toLp 2 (u, (1 : ℝ)))
    (hshort : ∀ w ∈ appendWindow L u, w ≠ 0 → ‖v‖ ≤ ‖w‖) :
    ZLattice.covolume (retainedWindow L u v) = ZLattice.covolume L / ‖v‖ := by
  let x := (k : ℝ)⁻¹ • l
  let R := L ⊔ ℤ ∙ x
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hvs : v.snd = (k : ℝ) := by rw [hv]; change 0 + (k : ℝ) * 1 = _; ring
  have hm : markedPreimage L (fun _ : Unit ↦ x) = R := by
    rw [markedPreimage_eq, Set.range_const]
  have : DiscreteTopology R := hm ▸ markedPreimage_discrete L (fun _ : Unit ↦ x) k (by
    intro i; change k • ((k : ℝ)⁻¹ • l) ∈ L
    rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀ hkR.ne']) hk.ne'
  have : IsZLattice ℝ R := ⟨by
    apply top_unique
    calc ⊤ = span ℝ (L : Set V) := IsZLattice.span_top.symm
         _ ≤ _ := span_mono (show (L : Set V) ⊆ R from fun _ hx ↦ Submodule.mem_sup_left hx)⟩
  have hindex := ZLattice.covolume_div_covolume_eq_relIndex' L R le_sup_left
  rw [show L.toAddSubgroup.relIndex R.toAddSubgroup = k from
    verticalWinner_index L u l hl k hk v hv hshort] at hindex
  have hD := (div_eq_iff (ZLattice.covolume_ne_zero R)).1 hindex
  rw [retained_eq_project_refinement L u l k hk v hv, covolume_project_horizontal R v
    (hvs ▸ hkR), hvs, hD]
  ring

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.gram_project_exchange
#print axioms SigabaNeo.Wall1.winnerCompression_gram
#print axioms SigabaNeo.Wall1.covolume_span_sq_eq_gram
#print axioms SigabaNeo.Wall1.covolume_project_horizontal
#print axioms SigabaNeo.Wall1.verticalWinner_covolume
