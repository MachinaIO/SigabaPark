module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit true

public section

open scoped InnerProductSpace

namespace SigabaNeo.Wall1

/-- Projecting the tail of a family perpendicular to its head factors its Gram determinant. -/
theorem det_gram_project_tail {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : Fin (n + 1) → E) :
    (Matrix.gram ℝ b).det = ‖b 0‖ ^ 2 *
      (Matrix.gram ℝ (fun i : Fin n ↦ (ℝ ∙ b 0)ᗮ.starProjection (b i.succ))).det := by
  let K := (ℝ ∙ b 0)ᗮ
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j ↦ inner ℝ (Fin.cons (α := fun _ ↦ E) (b 0) (fun k ↦ K.starProjection (b k.succ)) i) (b j)
  have hdet : M.det = (Matrix.gram ℝ b).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (Fin.cons (α := fun _ ↦ ℝ) 0 (fun i ↦ -(inner ℝ (b 0) (b i.succ) / ‖b 0‖ ^ 2))) 0 rfl
    intro i j
    refine Fin.cases (by simp [M]) (fun k ↦ ?_) i
    simp [M, K, Submodule.starProjection_singleton, inner_add_left, inner_neg_left, real_inner_smul_left,
      sub_eq_add_neg]
  have hzero (i : Fin n) : M i.succ 0 = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (K.starProjection_apply_mem _)
  have hminor : M.submatrix Fin.succ Fin.succ =
      Matrix.gram ℝ (fun i : Fin n ↦ K.starProjection (b i.succ)) := by
    ext i j
    change inner ℝ (K.starProjection _) _ = inner ℝ (K.starProjection _) (K.starProjection _)
    rw [← K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr
      (K.starProjection_apply_mem _)]
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hhead : M 0 0 = ‖b 0‖ ^ 2 := real_inner_self_eq_norm_sq _
  simp [hzero, hminor, hhead, K]

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.det_gram_project_tail
