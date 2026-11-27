module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential

set_option autoImplicit true

@[expose] public section
namespace SigabaNeo.Rogers

theorem ColumnCandidate.potential_eq_of_basis_eq {n : ℕ} {x : SL n}
    (a b : ColumnCandidate x) (hab : a.γ = b.γ) : a.potential = b.potential := by
  have gram (c : ColumnCandidate x) :
      let y := (x * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) c.γ).val
      y.transpose * y = c.r.transpose * c.r := by
    dsimp only
    rw [c.factor, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.k.transpose,
      c.orthogonal, Matrix.one_mul]
  have h := gram a
  rw [hab] at h
  replace h := (gram b).symm.trans h
  have rows (i : Fin n) : ∀ j, a.r i j = b.r i j := by
    apply wellFounded_lt.induction i
    intro i ih
    have diagonal_product (j : Fin n) : a.r i i * a.r i j = b.r i i * b.r i j := by
      have eq := congrArg (fun m : Matrix (Fin n) (Fin n) ℝ ↦ m i j) h
      simp only [Matrix.mul_apply, Matrix.transpose_apply] at eq
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at eq
      have rest : ∑ t ∈ Finset.univ.erase i, a.r t i * a.r t j =
          ∑ t ∈ Finset.univ.erase i, b.r t i * b.r t j := by
        apply Finset.sum_congr rfl
        intro t ht
        rcases lt_or_gt_of_ne (Finset.mem_erase.mp ht).1 with hl | hg
        · rw [ih t hl i, ih t hl j]
        · simp [a.triangular t i hg, b.triangular t i hg]
      linarith
    have diag : a.r i i = b.r i i := by
      nlinarith [diagonal_product i, a.positive i, b.positive i,
        sq_nonneg (a.r i i - b.r i i)]
    intro j
    have eq := diagonal_product j
    rw [diag] at eq
    exact mul_left_cancel₀ (b.positive i).ne' eq
  unfold ColumnCandidate.potential
  simp_rw [rows]

end SigabaNeo.Rogers
