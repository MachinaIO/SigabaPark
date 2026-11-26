module

public import Mathlib

set_option autoImplicit true

/-! # Projected blocks in Gram–Schmidt coordinates

The columns retain precisely the normalized Gram–Schmidt coordinates indexed by the block.
The block lattice is their integer span in coordinate space, with Euclidean length given by
the sum of squared coordinates. Its covolume is the product of the block's GSO lengths.
-/

public section

open InnerProductSpace Module
open scoped RealInnerProductSpace

namespace SigabaNeo.BKZ

noncomputable section

variable {n i k : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin n))

@[expose] def blockIndex (h : i + k ≤ n) (j : Fin k) : Fin n := ⟨i + j, by omega⟩

/-- Projected columns in the orthonormal frame of the block. -/
def blockMatrix (h : i + k ≤ n) : Matrix (Fin k) (Fin k) ℝ :=
  fun p q ↦ ⟪gramSchmidt ℝ b (blockIndex h p), b (blockIndex h q)⟫_ℝ /
    ‖gramSchmidt ℝ b (blockIndex h p)‖

/-- Removing the orthogonal projection onto the preceding span leaves every block
coordinate unchanged. -/
theorem blockMatrix_projected (h : i + k ≤ n) (p q : Fin k) :
    let P := Submodule.span ℝ (b '' {j : Fin n | j.val < i})
    let x := b (blockIndex h q)
    blockMatrix b h p q =
      ⟪gramSchmidt ℝ b (blockIndex h p), x - P.starProjection x⟫_ℝ /
        ‖gramSchmidt ℝ b (blockIndex h p)‖ := by
  intro P x
  let g := gramSchmidt ℝ b (blockIndex h p)
  have hP : P ≤ (ℝ ∙ g)ᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    apply (Submodule.mem_orthogonal_singleton_iff_inner_right).mpr
    apply gramSchmidt_inv_triangular
    change j.val < i + p.val
    change j.val < i at hj
    omega
  have hz := hP (P.starProjection_apply_mem x)
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hz
  simp [blockMatrix, inner_sub_right, g, x] at hz ⊢
  rw [hz, sub_zero]

theorem inner_diag (j : Fin n) :
    ⟪gramSchmidt ℝ b j, b j⟫_ℝ = ‖gramSchmidt ℝ b j‖ ^ 2 := by
  conv_lhs => rhs; rw [gramSchmidt_def'' ℝ b j]
  rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro q hq
  simp [real_inner_smul_right, gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.mp hq).ne']

theorem blockMatrix_det (h : i + k ≤ n) :
    (blockMatrix b h).det = ∏ j, ‖gramSchmidt ℝ b (blockIndex h j)‖ := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_congr rfl
    intro j _
    simp [blockMatrix, inner_diag, sq]
  · intro p q hp
    apply div_eq_zero_iff.mpr
    left
    apply gramSchmidt_inv_triangular
    change i + q.val < i + p.val
    exact Nat.add_lt_add_left hp i

def blockBasis (hb : LinearIndependent ℝ b) (h : i + k ≤ n) :
    Basis (Fin k) ℝ (Fin k → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' (blockMatrix b h).col
    (Matrix.linearIndependent_col_iff_isUnit.mpr ((blockMatrix b h).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (by
        rw [blockMatrix_det]
        exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ norm_ne_zero_iff.mpr
          (gramSchmidt_ne_zero _ hb))))) (by simp)

theorem blockBasis_apply_coord (hb : LinearIndependent ℝ b) (h : i + k ≤ n) (p q : Fin k) :
    blockBasis b hb h q p =
      ⟪gramSchmidt ℝ b (blockIndex h p), b (blockIndex h q)⟫_ℝ /
        ‖gramSchmidt ℝ b (blockIndex h p)‖ := by
  unfold blockBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rfl

abbrev blockLattice (hb : LinearIndependent ℝ b) (h : i + k ≤ n) :=
  Submodule.span ℤ (Set.range (blockBasis b hb h))

theorem blockLattice_covolume (hb : LinearIndependent ℝ b) (h : i + k ≤ n) :
    ZLattice.covolume (blockLattice b hb h) = ∏ j, ‖gramSchmidt ℝ b (blockIndex h j)‖ := by
  rw [ZLattice.covolume_eq_det _ ((blockBasis b hb h).restrictScalars ℤ)]
  have eq : Matrix.of (Subtype.val ∘ ((blockBasis b hb h).restrictScalars ℤ)) =
      (blockMatrix b h).transpose := by
    ext p q
    change (((blockBasis b hb h).restrictScalars ℤ p).val) q = _
    rw [Basis.restrictScalars_apply]
    unfold blockBasis
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    rfl
  rw [eq, Matrix.det_transpose, blockMatrix_det, abs_of_nonneg (by positivity)]

open MeasureTheory ZSpan

/-- Covolume of the original integer span, measured in the ambient Euclidean space. -/
theorem basis_covolume (a : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ZLattice.covolume (Submodule.span ℤ (Set.range a)) =
      ∏ j, ‖gramSchmidt ℝ a j‖ := by
  let h : finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis h a
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume (a.restrictScalars ℤ) e.toBasis,
    measureReal_congr (fundamentalDomain_ae_parallelepiped e.toBasis volume)]
  have vol : volume.real (parallelepiped e.toBasis) = 1 := by
    simpa [Measure.real] using congrArg ENNReal.toReal e.volume_parallelepiped
  rw [vol, mul_one]
  have eq : Subtype.val ∘ (a.restrictScalars ℤ) = (a : Fin n → _) := by
    ext j : 1
    exact a.restrictScalars_apply ℤ j
  rw [eq, gramSchmidtOrthonormalBasis_det]
  have diag (j : Fin n) : ⟪gramSchmidtOrthonormalBasis h a j, a j⟫_ℝ =
      ‖gramSchmidt ℝ a j‖ := by
    have hp := norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j a.linearIndependent)
    rw [gramSchmidtOrthonormalBasis_apply h
      ((gramSchmidtNormed_orthonormal a.linearIndependent).ne_zero j)]
    simp [gramSchmidtNormed, real_inner_smul_left, inner_diag, sq, hp]
  simp_rw [diag]
  exact abs_of_nonneg (by positivity)

end

end SigabaNeo.BKZ
