module

public import Definitions.Def_LatticeAttack_Research_Wall1_GramProduct

set_option autoImplicit true

public section

namespace SigabaNeo.Wall1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

private instance (b : Fin k → E) : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range b)

private instance (b : Fin k → E) : CompleteSpace (Submodule.span ℝ (Set.range b)) :=
  FiniteDimensional.complete ℝ _

/-- Orthogonal projection away from a finite family. -/
noncomputable abbrev prefixProjection (b : Fin k → E) : E →L[ℝ] E := by
  letI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  letI : CompleteSpace (Submodule.span ℝ (Set.range b)) := FiniteDimensional.complete ℝ _
  exact (Submodule.span ℝ (Set.range b))ᗮ.starProjection

/-- Appending a vector multiplies the Gram determinant by its squared projected length. -/
theorem projectedLength_sq_mul_det (b : Fin k → E) (w : E) :
    ‖prefixProjection b w‖ ^ 2 * (Matrix.gram ℝ b).det =
      (Matrix.gram ℝ (Fin.snoc (α := fun _ ↦ E) b w)).det := by
  classical
  let K := Submodule.span ℝ (Set.range b)
  let v := Fin.snoc (α := fun _ ↦ E) b w
  let A := Matrix.gram ℝ v
  let row (x : E) (j : Fin (k+1)) := inner ℝ x (v j)
  let D : E →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ (A.updateRow (Fin.last k) (row x)).det
      map_add' := fun x y ↦ by
        rw [show row (x+y) = row x + row y by ext; simp [row, inner_add_left],
          Matrix.det_updateRow_add]
      map_smul' := fun c x ↦ by
        rw [show row (c • x) = c • row x by ext; simp [row, real_inner_smul_left],
          Matrix.det_updateRow_smul]; rfl }
  have hk : K ≤ D.ker := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    change (A.updateRow _ (row (b i))).det = 0
    rw [show row (b i) = A i.castSucc by ext; simp [A, row, v, Matrix.gram_apply]]
    exact Matrix.det_updateRow_eq_zero (Fin.castSucc_ne_last i))
  let p := Kᗮ.starProjection w
  have hd : D w = D p := by
    have h : D (K.starProjection w) = 0 := hk (K.starProjection_apply_mem w)
    simpa only [map_add, h, zero_add, p] using congrArg D (K.starProjection_add_starProjection_orthogonal w).symm
  have hw : D w = A.det := by
    change (A.updateRow _ (row w)).det = _
    rw [show row w = A (Fin.last k) by ext; simp [A, row, v, Matrix.gram_apply],
      Matrix.updateRow_eq_self]
  let M := A.updateRow (Fin.last k) (row p)
  have hz (i : Fin k) : M (Fin.last k) i.castSucc = 0 := by
    simp only [M, Matrix.updateRow_self, row, v, Fin.snoc_castSucc]
    exact (Submodule.mem_orthogonal' _ _).mp (Kᗮ.starProjection_apply_mem w) _
      (Submodule.subset_span ⟨i, rfl⟩)
  have hp : M (Fin.last k) (Fin.last k) = ‖p‖ ^ 2 := by
    simp only [M, Matrix.updateRow_self, row, v, Fin.snoc_last]
    rw [← real_inner_self_eq_norm_sq, ← Kᗮ.inner_starProjection_left_eq_right,
      Kᗮ.starProjection_eq_self_iff.mpr (Kᗮ.starProjection_apply_mem w)]
  have hm : M.submatrix Fin.castSucc Fin.castSucc = Matrix.gram ℝ b := by
    ext i j
    simp [M, Matrix.updateRow_ne, Fin.castSucc_ne_last, A, v, Matrix.gram_apply]
  change _ = A.det
  rw [← hw, hd]
  change ‖p‖ ^ 2 * (Matrix.gram ℝ b).det = M.det
  rw [Matrix.det_succ_row M (Fin.last k), Fin.sum_univ_castSucc]
  simp [hz, hp, hm, Even.neg_one_pow (show Even (k+k) from ⟨k, rfl⟩)]

/-- The positive prefix determinant permits division and the nonnegative square root. -/
theorem projectedLength_eq_sqrt (b : Fin k → E) (w : E) (hb : 0 < (Matrix.gram ℝ b).det) :
    ‖prefixProjection b w‖ =
      Real.sqrt ((Matrix.gram ℝ (Fin.snoc (α := fun _ ↦ E) b w)).det / (Matrix.gram ℝ b).det) := by
  rw [← projectedLength_sq_mul_det, mul_div_cancel_right₀ _ hb.ne', Real.sqrt_sq (norm_nonneg _)]

/-- A nonzero projected lattice vector bounds the infimum of nonzero projected lengths. -/
theorem projectedMinimum_le_sqrt (b : Fin k → E) (L : AddSubgroup E) (w : E) (hw : w ∈ L)
    (hp : prefixProjection b w ≠ 0) (hb : 0 < (Matrix.gram ℝ b).det) :
    sInf {r : ℝ | ∃ x ∈ L, prefixProjection b x ≠ 0 ∧ ‖prefixProjection b x‖ = r} ≤
      Real.sqrt ((Matrix.gram ℝ (Fin.snoc (α := fun _ ↦ E) b w)).det / (Matrix.gram ℝ b).det) := by
  rw [← projectedLength_eq_sqrt b w hb]
  apply csInf_le
  swap
  · exact ⟨w, hw, hp, rfl⟩
  exact ⟨0, fun _ ⟨_, _, _, h⟩ ↦ h ▸ norm_nonneg _⟩

end SigabaNeo.Wall1

#print axioms SigabaNeo.Wall1.projectedLength_sq_mul_det
#print axioms SigabaNeo.Wall1.projectedLength_eq_sqrt
#print axioms SigabaNeo.Wall1.projectedMinimum_le_sqrt
