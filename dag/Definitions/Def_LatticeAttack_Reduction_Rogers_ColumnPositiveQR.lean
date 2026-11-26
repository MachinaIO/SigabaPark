module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Definitions.Def_LatticeAttack_Reduction_BKZ_Geometry

set_option autoImplicit true

@[expose] public section
open InnerProductSpace
namespace SigabaNeo.Rogers

theorem columnPositiveQR {n : ℕ} (x : SL n) :
    ∃ k r : Matrix (Fin n) (Fin n) ℝ, k.transpose * k = 1 ∧ x.val = k * r ∧
      (∀ i, 0 < r i i) ∧ (∀ i j, j < i → r i j = 0) := by
  classical
  let f (j : Fin n) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (x.val.col j)
  have hf : LinearIndependent ℝ f :=
    (Matrix.linearIndependent_cols_of_det_ne_zero (A := x.val) (by rw [x.property]; norm_num)).map'
      (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap (LinearEquiv.ker _)
  let dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis dim f
  refine ⟨fun i j ↦ e j i, fun i j ↦ inner ℝ (e i) (f j), ?_, ?_, ?_,
    fun _ _ h ↦ gramSchmidtOrthonormalBasis_inv_triangular dim f h⟩
  · ext i j
    change (∑ t, e i t * e j t) = (1 : Matrix (Fin n) (Fin n) ℝ) i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, PiLp.inner_apply,
      real_inner_eq_re_inner, mul_comm] using (orthonormal_iff_ite.mp e.orthonormal i j)
  · ext i j
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v i) (e.sum_repr' (f j))
    change x.val i j = ∑ t, e t i * inner ℝ (e t) (f j)
    simpa [Matrix.mul_apply, mul_comm, f, Matrix.col] using h.symm
  · intro i
    have hp := norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hf)
    change 0 < inner ℝ (gramSchmidtOrthonormalBasis dim f i) (f i)
    rw [gramSchmidtOrthonormalBasis_apply dim ((gramSchmidtNormed_orthonormal hf).ne_zero i)]
    simpa [gramSchmidtNormed, real_inner_smul_left, SigabaNeo.BKZ.inner_diag, sq, hp] using
      (lt_of_le_of_ne (norm_nonneg _) hp.symm)

end SigabaNeo.Rogers
