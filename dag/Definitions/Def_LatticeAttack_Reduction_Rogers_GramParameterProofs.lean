module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnGramParameters
public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnPositiveQR

set_option autoImplicit true

@[expose] public section
noncomputable section
open InnerProductSpace
namespace SigabaNeo.Rogers

theorem gramParamsRecovered (d : ℕ) (_ : 1 ≤ d) (g : SL (d+1)) (p : ColumnParameters d)
    (h : HasColumnParameters g p) : gramColumnParameters g = p := by
  classical
  obtain ⟨k,u,a,hk,ha,hu,hz,hg,ht,hv⟩ := h
  let e (i : Fin (d+1)) : E (d+1) := WithLp.toLp 2 (k.col i)
  have orth : Orthonormal ℝ e := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simpa [e, Matrix.col, Matrix.mul_apply, Matrix.one_apply, PiLp.inner_apply,
      real_inner_eq_re_inner, mul_comm] using congrArg (fun m : Matrix _ _ ℝ ↦ m i j) hk
  have expand (j : Fin (d+1)) : qrColumn g j = ∑ i, (a i * u i j) • e i := by
    ext t
    simp [qrColumn, hg, Matrix.mul_apply, Matrix.diagonal_apply, e, Matrix.col,
      mul_comm, mul_left_comm]
  have coeff (i j : Fin (d+1)) : inner ℝ (e i) (qrColumn g j) = a i * u i j := by
    rw [expand, inner_sum]
    simp [real_inner_smul_right, orthonormal_iff_ite.mp orth]
  have ratio (i j : Fin (d+1)) :
      inner ℝ (a i • e i) (qrColumn g j) / ‖a i • e i‖ ^ 2 = u i j := by
    simp [real_inner_smul_left, coeff, norm_smul, Real.norm_eq_abs, abs_of_pos (ha i),
      orth.1 i]
    field_simp [(ha i).ne']
  have residual (j : Fin (d+1)) : qrResidual g j = a j • e j := by
    apply wellFounded_lt.induction j
    intro j ih
    have eqn := gramSchmidt_def'' ℝ (qrColumn g) j
    change qrColumn g j = qrResidual g j + ∑ i ∈ Finset.Iio j,
      (inner ℝ (qrResidual g i) (qrColumn g j) / ‖qrResidual g i‖ ^ 2) • qrResidual g i at eqn
    apply add_right_cancel (b := ∑ i ∈ Finset.Iio j,
      (inner ℝ (qrResidual g i) (qrColumn g j) / ‖qrResidual g i‖ ^ 2) • qrResidual g i)
    rw [← eqn]
    conv_lhs => rw [expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hu, mul_one]
    congr 1
    symm
    calc
      _ = ∑ i ∈ Finset.Iio j, (a i * u i j) • e i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (Finset.mem_Iio.mp hi), ratio, smul_smul, mul_comm]
      _ = _ := by
        apply Finset.sum_subset_zero_on_sdiff
        · intro i hi
          simp [(Finset.mem_Iio.mp hi).ne]
        · intro i hi
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
            Finset.mem_Iio, not_lt] at hi
          simp [hz i j (lt_of_le_of_ne hi.2 hi.1.symm)]
        · simp
  apply Prod.ext
  · rw [← ht]
    funext i
    simp [gramColumnParameters, residual, norm_smul, orth.1, Real.norm_eq_abs,
      abs_of_pos (ha _)]
  · rw [← hv]
    funext i
    exact (by change inner ℝ (qrResidual g _) _ / ‖qrResidual g _‖ ^ 2 = _
              rw [residual, ratio])

theorem gramParamsRealized (d : ℕ) (hd : 1 ≤ d) (g : SL (d+1)) :
    HasColumnParameters g (gramColumnParameters g) := by
  obtain ⟨k,r,hk,hg,hp,hz⟩ := columnPositiveQR g
  let a i := r i i
  let u : Matrix (Fin (d+1)) (Fin (d+1)) ℝ := fun i j ↦ r i j / a i
  have hr : r = Matrix.diagonal a * u := by
    ext i j
    rw [Matrix.diagonal_mul]
    change r i j = r i i * (r i j / r i i)
    field_simp [(hp i).ne']
  have h : HasColumnParameters g
      ((fun i ↦ Real.log (a i.succ) - Real.log (a i.castSucc)), fun i ↦ u i.val.1 i.val.2) := by
    refine ⟨k,u,a,hk,hp,fun i ↦ div_self (hp i).ne',fun i j hij ↦ ?_,?_,rfl,rfl⟩
    · simp [u,hz i j hij]
    · rw [Matrix.mul_assoc, ← hr, hg]
  rw [gramParamsRecovered d hd g _ h]
  exact h

#print axioms gramParamsRecovered
#print axioms gramParamsRealized
end SigabaNeo.Rogers
