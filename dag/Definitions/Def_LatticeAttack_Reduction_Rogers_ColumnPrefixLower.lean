module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRPotential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit true

@[expose] public section

namespace SigabaNeo.Rogers

/-- For a fixed prefix, factor its integral Gram determinant through the triangular block.
Compactness of the entrywise unit box bounds the other determinant uniformly. -/
private theorem fixedPrefixLower {n : ℕ} (x : SL n) (k : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ c : ColumnCandidate x,
      L ≤ ∏ j : Fin n with j.val < k, c.r j j ^ 2 := by
  classical
  let I := {i : Fin n // i.val < k}
  let e : I → Fin n := Subtype.val
  let A (q : Matrix (Fin n) (Fin n) ℝ) := (x⁻¹.val * q).submatrix id e
  let F (q : Matrix (Fin n) (Fin n) ℝ) := ((A q).transpose * A q).det
  have ha : Continuous A := (continuous_const.matrix_mul continuous_id).matrix_submatrix id e
  have hf : Continuous F := (ha.matrix_transpose.matrix_mul ha).matrix_det
  let box := Set.pi Set.univ (fun _ : Fin n ↦ Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (-1 : ℝ) 1))
  have hb : IsCompact box := isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  obtain ⟨D, hD⟩ := hb.bddAbove_image hf.continuousOn
  refine ⟨1 / (max D 1), one_div_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right ..)), ?_⟩
  intro c
  have hq : c.k ∈ box := by
    intro i _ j _
    have h := congrArg (fun m : Matrix (Fin n) (Fin n) ℝ ↦ m j j) c.orthogonal
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have hs := Finset.single_le_sum (f := fun t ↦ c.k t j * c.k t j)
      (fun t _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
    constructor <;> nlinarith
  have hF := (hD (Set.mem_image_of_mem F hq)).trans (le_max_left D 1)
  let R := c.r.submatrix e e
  let Z := c.γ.val.submatrix id e
  let g := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) c.γ
  have hγ : g.val = (x⁻¹.val * c.k) * c.r := by
    rw [Matrix.mul_assoc, ← c.factor]
    change g.val = (x⁻¹ * (x * g)).val
    simp
  have hfac : Z.map (Int.castRingHom ℝ) = A c.k * R := by
    change g.val.submatrix id e = _
    rw [hγ]
    ext i j
    change (∑ t : Fin n, (x⁻¹.val * c.k) i t * c.r t (e j)) =
      ∑ t : I, (x⁻¹.val * c.k) i (e t) * c.r (e t) (e j)
    rw [← Finset.sum_subtype (p := fun t : Fin n ↦ t.val < k)
      (Finset.univ.filter fun t : Fin n ↦ t.val < k) (by simp)
      (fun t ↦ (x⁻¹.val * c.k) i t * c.r t (e j))]
    symm
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro t _ ht
    have hj := j.property
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [c.triangular t (e j) (show j.val.val < t.val by omega), mul_zero]
  have hz : 0 < (Z.transpose * Z).det := by
    have h := Matrix.PosDef.conjTranspose_mul_self c.γ.val
      (Matrix.mulVec_injective_of_det_ne_zero (by rw [c.γ.property]; decide))
    exact (h.submatrix (e := e) Subtype.val_injective).det_pos
  have hcast : (1 : ℝ) ≤ (((Z.transpose * Z).det : ℤ) : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ _ by omega)
  change (1 : ℝ) ≤ (Int.castRingHom ℝ) _ at hcast
  rw [RingHom.map_det] at hcast
  change 1 ≤ ((Z.transpose * Z).map (Int.castRingHom ℝ)).det at hcast
  rw [Matrix.map_mul] at hcast
  change 1 ≤ ((Z.map (Int.castRingHom ℝ)).transpose * Z.map (Int.castRingHom ℝ)).det at hcast
  rw [hfac, Matrix.transpose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc (A c.k).transpose, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose] at hcast
  have hdet : R.det = ∏ j : I, c.r (e j) (e j) :=
    Matrix.det_of_isUpperTriangular (fun i j h ↦ c.triangular _ _ h)
  have hp : R.det ^ 2 = ∏ j : Fin n with j.val < k, c.r j j ^ 2 := by
    rw [hdet, ← Finset.prod_pow]
    exact (Finset.prod_subtype (p := fun t : Fin n ↦ t.val < k)
      (Finset.univ.filter fun t : Fin n ↦ t.val < k) (by simp) (fun j ↦ c.r j j ^ 2)).symm
  rw [← hp]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_right ..))).2
  calc
    1 ≤ R.det * (F c.k * R.det) := hcast
    _ = R.det ^ 2 * F c.k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hF (sq_nonneg _)

/-- All squared prefix covolumes of integral basis changes have a common positive lower bound. -/
theorem column_prefix_covolume_sq_lower : ∀ d : ℕ, 1 ≤ d → ∀ x : SL (d + 1),
    ∃ L : ℝ, 0 < L ∧ ∀ (c : ColumnCandidate x) (k : ℕ), k ≤ d + 1 →
      L ≤ ∏ j : Fin (d + 1) with j.val < k, c.r j j ^ 2 := by
  intro d _ x
  choose L hL h using fixedPrefixLower x
  suffices aux : ∀ m : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ k ≤ m, a ≤ L k by
    obtain ⟨a, ha, hb⟩ := aux (d+1)
    exact ⟨a, ha, fun c k hk ↦ (hb k hk).trans (h k c)⟩
  intro m
  induction m with
  | zero => exact ⟨L 0, hL 0, fun k hk ↦ by simp [Nat.eq_zero_of_le_zero hk]⟩
  | succ m ih =>
    obtain ⟨a, ha, hb⟩ := ih
    exact ⟨min a (L (m+1)), lt_min ha (hL _), fun k hk ↦ by
      rcases Nat.lt_or_eq_of_le hk with hk | rfl
      · exact (min_le_left ..).trans (hb k (by omega))
      · exact min_le_right ..⟩

end SigabaNeo.Rogers
