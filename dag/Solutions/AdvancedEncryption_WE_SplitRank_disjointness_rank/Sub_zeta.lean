import Mathlib.Combinatorics.Colex
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

theorem solution (h : ℕ) :
    let D : Matrix (Finset (Fin h)) (Finset (Fin h)) (ZMod 2) :=
      Matrix.of fun s t ↦ if Disjoint s t then 1 else 0
    IsUnit D ∧ D.rank = 2 ^ h ∧
      ∀ {m n r : ℕ} (U : Matrix (Fin m) (Fin r) (ZMod 2))
        (V : Matrix (Fin r) (Fin n) (ZMod 2))
        (rows : Finset (Fin h) → Fin m) (cols : Finset (Fin h) → Fin n),
        (U * V).submatrix rows cols = D → 2 ^ h ≤ r := by
  classical
  dsimp only
  let D : Matrix (Finset (Fin h)) (Finset (Fin h)) (ZMod 2) :=
    Matrix.of fun s t ↦ if Disjoint s t then 1 else 0
  change IsUnit D ∧ D.rank = 2 ^ h ∧ _
  let c : Equiv.Perm (Finset (Fin h)) := compl_involutive.toPerm
  let _ : Fintype (Colex (Finset (Fin h))) := Fintype.ofEquiv _ toColex
  let Z : Matrix (Colex (Finset (Fin h))) (Colex (Finset (Fin h))) (ZMod 2) :=
    Matrix.of fun s t ↦ if ofColex s ⊆ ofColex t then 1 else 0
  have upper : Z.IsUpperTriangular := by
    intro i j hji
    apply ite_eq_right
    intro hij
    exact (not_le_of_gt hji) (Finset.Colex.toColex_le_toColex_of_subset hij)
  have detZ : Z.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular upper]
    simp [Z]
  have unitZ : IsUnit Z := (Matrix.isUnit_iff_isUnit_det _).2 (detZ ▸ isUnit_one)
  have permuted : Z.submatrix toColex (c.trans toColex) = D := by
    ext s t
    change (if s ⊆ tᶜ then _ else _) = _
    simp [D, Finset.subset_compl_iff_disjoint_right]
  have unitD : IsUnit D := permuted ▸ (Matrix.isUnit_submatrix_equiv _ _).2 unitZ
  have rankD : D.rank = 2 ^ h := by simp [Matrix.rank_of_isUnit D unitD, Fintype.card_finset]
  refine ⟨unitD, rankD, ?_⟩
  intro m n r U V rows cols hD
  calc
    2 ^ h = D.rank := rankD.symm
    _ = ((U * V).submatrix rows cols).rank := congrArg Matrix.rank hD.symm
    _ ≤ (U * V).rank := Matrix.rank_submatrix_le _ _ _
    _ ≤ U.rank := Matrix.rank_mul_le_left _ _
    _ ≤ r := by simpa using U.rank_le_card_width
