import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnRightActions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit true

noncomputable section
open Matrix MeasureTheory
namespace SigabaNeo.Rogers

/-- Linear part of right multiplication by an upper unitriangular matrix in strict
upper-entry coordinates. -/
def upperRightLinear {n : ℕ} (b : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (UpperEntry n) (UpperEntry n) ℝ :=
  fun i j ↦ if i.val.1 = j.val.1 then b j.val.2 i.val.2 else 0

theorem upperRightLinear_det {n : ℕ} (b : Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i, b i i = 1) (hz : ∀ i j, j < i → b i j = 0) :
    (upperRightLinear b).det = 1 := by
  let : LinearOrder (UpperEntry n) := LinearOrder.lift'
    (fun i : UpperEntry n ↦ toLex i.val) (toLex.injective.comp Subtype.val_injective)
  apply (Matrix.det_of_isLowerTriangular _ ?_).trans
  · simp [upperRightLinear, hb]
  · intro i j h
    change toLex i.val < toLex j.val at h
    rcases Prod.Lex.toLex_lt_toLex.mp h with h | ⟨h, h'⟩
    · simp [upperRightLinear, h.ne]
    · simp [upperRightLinear, h, hz _ _ h']

theorem upperRightAffine_map_volume {n : ℕ} (b : Matrix (Fin n) (Fin n) ℝ)
    (hb : ∀ i, b i i = 1) (hz : ∀ i j, j < i → b i j = 0) :
    Measure.map (fun u ↦ (fun i : UpperEntry n ↦ b i.val.1 i.val.2) +
      (upperRightLinear b).toLin' u) volume = volume := by
  have h := upperRightLinear_det b hb hz
  rw [show (fun u ↦ _ + (upperRightLinear b).toLin' u) =
      ((fun i : UpperEntry n ↦ b i.val.1 i.val.2) + ·) ∘ (upperRightLinear b).toLin' by rfl,
    ← Measure.map_map (measurable_const_add _) (LinearMap.continuous_of_finiteDimensional _).measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [h]; norm_num), h]
  simp [map_add_left_eq_self]

theorem upperDiagonal_map_volume {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) :
    Measure.map (fun (u : UpperEntry n → ℝ) i ↦ u i * s i.val.2 / s i.val.1) volume =
      ENNReal.ofReal (∏ i : UpperEntry n, s i.val.2 / s i.val.1)⁻¹ • volume := by
  let D := fun i : UpperEntry n ↦ s i.val.2 / s i.val.1
  have h : 0 < ∏ i, D i := Finset.prod_pos fun i _ ↦ div_pos (hs _) (hs _)
  have e : (fun (u : UpperEntry n → ℝ) i ↦ u i * s i.val.2 / s i.val.1) =
      (diagonal D).toLin' := by
    funext u i
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal, D]
    ring
  rw [e, Real.map_matrix_volume_pi_eq_smul_volume_pi (by simpa using h.ne'),
    Matrix.det_diagonal, abs_of_pos (inv_pos.mpr h)]


theorem upperRightAffine_apply {n : ℕ} (u b : Matrix (Fin n) (Fin n) ℝ)
    (hu : ∀ i, u i i = 1) (hz : ∀ i j, j < i → u i j = 0) (i : UpperEntry n) :
    (u * b) i.val.1 i.val.2 = b i.val.1 i.val.2 +
      (upperRightLinear b).toLin' (fun j ↦ u j.val.1 j.val.2) i := by
  classical
  rw [Matrix.mul_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i.val.1), hu, one_mul,
    add_comm, Matrix.toLin'_apply]
  congr 1
  change _ = ∑ j : UpperEntry n, upperRightLinear b i j * u j.val.1 j.val.2
  symm
  apply Finset.sum_bij_ne_zero (fun j _ _ ↦ j.val.2)
  · intro j _ h
    by_cases e : i.val.1 = j.val.1
    · exact Finset.mem_erase.mpr ⟨(e ▸ j.property).ne', Finset.mem_univ _⟩
    · simp [upperRightLinear,e] at h
  · intro j _ h k _ h' e
    have row (l : UpperEntry n) (h : upperRightLinear b i l * u l.val.1 l.val.2 ≠ 0) :
        i.val.1 = l.val.1 := by
      by_contra he
      simp [upperRightLinear, he] at h
    exact Subtype.ext (Prod.ext ((row j h).symm.trans (row k h')) e)
  · intro k hk h
    have hlt : i.val.1 < k := by
      rcases lt_trichotomy i.val.1 k with h | h | h
      · exact h
      · exact False.elim ((Finset.mem_erase.mp hk).1 h.symm)
      · simp [hz _ _ h] at *
    refine ⟨⟨(i.val.1,k), hlt⟩, Finset.mem_univ _, ?_, rfl⟩
    simpa [upperRightLinear, mul_comm] using h
  · intro j _ h
    by_cases e : i.val.1 = j.val.1
    · simp [upperRightLinear, e, mul_comm]
    · simp [upperRightLinear,e] at h

theorem columnChart_map_upperAffine {d : ℕ} {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) (b : SL (d+1)) (hb : ∀ i, b.val i i = 1)
    (hz : ∀ i j, j < i → b.val i j = 0) :
    ((groupHaar (d+1)).map f).map (fun p ↦ (p.1,
      (fun i : UpperEntry (d+1) ↦ b.val i.val.1 i.val.2) +
        (upperRightLinear b.val).toLin' p.2)) = (groupHaar (d+1)).map f := by
  apply columnChart_map_rightAction hf b
  · exact measurable_fst.prodMk (measurable_const.add
      ((LinearMap.continuous_of_finiteDimensional _).measurable.comp measurable_snd))
  · intro g
    obtain ⟨u, hu, hl, he, hp⟩ :=
      columnParams_mul_unitriangular ((hf.2 g _).mpr rfl) hb hz
    have hu' : (fun i : UpperEntry (d+1) ↦ u i.val.1 i.val.2) = (f g).2 := funext he
    simp_rw [upperRightAffine_apply u b.val hu hl, hu'] at hp
    exact hp

#print axioms upperRightAffine_map_volume
#print axioms upperDiagonal_map_volume
#print axioms columnChart_map_upperAffine
end SigabaNeo.Rogers
