import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnRightJacobians

set_option autoImplicit true

noncomputable section
open Matrix
namespace SigabaNeo.Rogers

private theorem upper_mul_diag {n : ℕ} {a b : Matrix (Fin n) (Fin n) ℝ}
    (ha : a.IsUpperTriangular) (hb : b.IsUpperTriangular) (i : Fin n) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ h
    rcases lt_or_gt_of_ne h with h | h
    · simp [ha h]
    · simp [hb h]
  · simp

/-- The upper triangular subgroup with positive diagonal in the real special linear group. -/
def columnBorel (n : ℕ) : Subgroup (SL n) where
  carrier := {b | b.val.IsUpperTriangular ∧ ∀ i, 0 < b.val i i}
  one_mem' := by
    constructor
    · intro i j h
      exact Matrix.one_apply_ne (ne_of_gt h)
    · intro i
      change 0 < (1 : Matrix _ _ ℝ) i i
      simp
  mul_mem' := by
    rintro a b ⟨ha, pa⟩ ⟨hb, pb⟩
    refine ⟨ha.mul hb, fun i ↦ ?_⟩
    change 0 < (a.val * b.val) i i
    rw [upper_mul_diag ha hb]
    exact mul_pos (pa i) (pb i)
  inv_mem' := by
    rintro a ⟨ha,pa⟩
    let :=  Matrix.invertibleOfIsUnitDet a.val (by rw [a.property]; exact isUnit_one)
    have he : a⁻¹.val = a.val⁻¹ := by
      rw [Matrix.inv_def, a.property]
      simp
    have hi : a⁻¹.val.IsUpperTriangular := he ▸ blockTriangular_inv_of_blockTriangular ha
    refine ⟨hi, fun i ↦ ?_⟩
    have h := upper_mul_diag ha hi i
    have e : a.val * a⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel a)
    rw [e, Matrix.one_apply_eq] at h
    exact pos_of_mul_pos_right (h ▸ zero_lt_one) (pa i).le

/-- Logarithms of the unique normalized diagonal with the prescribed adjacent log ratios. -/
def columnDiagLogs {d : ℕ} (t : Fin d → ℝ) (i : Fin (d+1)) : ℝ :=
  Fin.partialSum t i - (∑ j, Fin.partialSum t j) / (d+1)

theorem columnDiagLogs_sum {d : ℕ} (t : Fin d → ℝ) : ∑ i, columnDiagLogs t i = 0 := by
  simp [columnDiagLogs, Finset.sum_sub_distrib]
  field_simp
  ring

theorem columnDiagLogs_diff {d : ℕ} (t : Fin d → ℝ) (i : Fin d) :
    columnDiagLogs t i.succ - columnDiagLogs t i.castSucc = t i := by
  simp [columnDiagLogs, Fin.partialSum_succ]

def columnUpperMatrix {n : ℕ} (v : UpperEntry n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if h : i < j then v ⟨(i,j),h⟩ else if i = j then 1 else 0

theorem columnUpperMatrix_tri {n : ℕ} (v : UpperEntry n → ℝ) :
    (columnUpperMatrix v).IsUpperTriangular := by
  intro i j h
  change j < i at h
  simp [columnUpperMatrix,h.not_gt,h.ne']

def columnBorelSection {d : ℕ} (p : ColumnParameters d) : columnBorel (d+1) := by
  let a := fun i ↦ Real.exp (columnDiagLogs p.1 i)
  let u := columnUpperMatrix p.2
  have hu := columnUpperMatrix_tri p.2
  let b := diagonal a * u
  have hb : b.det = 1 := by
    rw [Matrix.det_mul, det_diagonal, det_of_isUpperTriangular hu]
    simp [columnUpperMatrix,a,← Real.exp_sum,columnDiagLogs_sum]
  refine ⟨⟨b,hb⟩, ?_, ?_⟩
  · intro i j h
    change (diagonal a * u) i j = 0
    simp [diagonal_mul,u,hu h]
  · intro i
    change 0 < (diagonal a * u) i i
    simp [diagonal_mul,u,columnUpperMatrix,a,Real.exp_pos]

theorem columnBorelSection_params {d : ℕ} (p : ColumnParameters d) :
    HasColumnParameters (columnBorelSection p).val p := by
  refine ⟨1, columnUpperMatrix p.2, fun i ↦ Real.exp (columnDiagLogs p.1 i),
    by simp, fun _ ↦ Real.exp_pos _, by simp [columnUpperMatrix], ?_, by simp [columnBorelSection],
    ?_, ?_⟩
  · exact fun _ _ h ↦ columnUpperMatrix_tri _ h
  · funext i
    simp [columnDiagLogs_diff]
  · funext i
    simp [columnUpperMatrix, i.property]

theorem columnBorelSection_surjective (d : ℕ) :
    Function.Surjective (columnBorelSection (d := d)) := by
  intro b
  let a (i : Fin (d+1)) := b.val.val i i
  have ha : ∀ i, 0 < a i := b.property.2
  have ht : b.val.val.IsUpperTriangular := b.property.1
  have hp : ∏ i, a i = 1 := (det_of_isUpperTriangular ht).symm.trans b.val.property
  let t (i : Fin d) := Real.log (a i.succ) - Real.log (a i.castSucc)
  let v (i : UpperEntry (d+1)) := b.val.val i.val.1 i.val.2 / a i.val.1
  have diff (i : Fin (d+1)) : columnDiagLogs t i - Real.log (a i) =
      columnDiagLogs t 0 - Real.log (a 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      have h := columnDiagLogs_diff t j
      dsimp only [t] at h
      linarith
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ diff i)
  rw [Finset.sum_sub_distrib, columnDiagLogs_sum, ← Real.log_prod (fun i _ ↦ (ha i).ne'),
    hp, Real.log_one, sub_zero] at hsum
  have hc : columnDiagLogs t 0 - Real.log (a 0) = 0 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact (mul_eq_zero.mp hsum.symm).resolve_left (by positivity)
  have he (i) : Real.exp (columnDiagLogs t i) = a i := by
    rw [sub_eq_zero.mp ((diff i).trans hc), Real.exp_log (ha i)]
  refine ⟨(t,v), Subtype.ext (Subtype.ext ?_)⟩
  ext i j
  change (diagonal (fun i ↦ Real.exp (columnDiagLogs t i)) * columnUpperMatrix v) i j = _
  rw [diagonal_mul,he]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [columnUpperMatrix, h, v]
    field_simp [(ha i).ne']
  · simp [columnUpperMatrix, a]
  · simp [columnUpperMatrix, h.not_gt, h.ne', ht h]

/-- Restricting any column chart to the positive triangular subgroup gives an equivalence. -/
def columnBorelEquiv {d : ℕ} {f : SL (d+1) → ColumnParameters d} (hf : IsColumnChart f) :
    columnBorel (d+1) ≃ ColumnParameters d where
  toFun b := f b.val
  invFun := columnBorelSection
  right_inv p := (hf.2 _ _).mp (columnBorelSection_params p)
  left_inv b := by
    obtain ⟨p,rfl⟩ := columnBorelSection_surjective d b
    exact congrArg columnBorelSection ((hf.2 _ _).mp (columnBorelSection_params p))

theorem continuous_columnBorelSection (d : ℕ) : Continuous (columnBorelSection (d := d)) := by
  have h (i : Fin (d+1)) : Continuous (fun p : ColumnParameters d ↦ Fin.partialSum p.1 i) := by
    induction i using Fin.induction with
    | zero => simpa only [Fin.partialSum_zero] using (continuous_const (y := (0 : ℝ)))
    | succ j ih =>
      simp only [Fin.partialSum_succ]
      exact ih.add ((continuous_apply j).comp continuous_fst)
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.mul
  · apply Continuous.matrix_diagonal
    apply continuous_pi
    intro i
    exact ((h i).sub ((continuous_finsetSum _ (fun j _ ↦ h j)).div_const _)).rexp
  · apply continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    dsimp [columnUpperMatrix]
    split <;> fun_prop

def columnBorelMeasurableEquiv {d : ℕ} {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) : columnBorel (d+1) ≃ᵐ ColumnParameters d where
  toEquiv := columnBorelEquiv hf
  measurable_toFun := hf.1.comp measurable_subtype_coe
  measurable_invFun := by
    let : BorelSpace (SL (d+1)) := ⟨rfl⟩
    exact (continuous_columnBorelSection d).measurable

theorem columnBorelSection_mul {d : ℕ} {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) (g : SL (d+1)) (b : columnBorel (d+1)) :
    columnBorelSection (f (g * b.val)) = columnBorelSection (f g) * b := by
  obtain ⟨k,u,a,hk,ha,hu,hz,hg,ht,hv⟩ := (hf.2 g _).mpr rfl
  have hU : u.det = 1 := by
    rw [det_of_isUpperTriangular (M := u) (fun {_ _} h ↦ hz _ _ h)]
    simp [hu]
  have hdet := congrArg Matrix.det hg
  simp only [g.property, det_mul, det_diagonal, hU, mul_one] at hdet
  have hkdet := congrArg Matrix.det hk
  simp only [det_mul, det_transpose, det_one] at hkdet
  have hp := Finset.prod_pos (s := Finset.univ) (fun i _ ↦ ha i)
  have hkpos : 0 < k.det := by by_contra! h; nlinarith [mul_nonpos_of_nonpos_of_nonneg h hp.le]
  have hk1 : k.det = 1 := by nlinarith
  let m : columnBorel (d+1) := ⟨⟨diagonal a * u, by simpa [hU, hk1] using hdet.symm⟩, by
    intro i j h
    simp [diagonal_mul, hz i j h], fun i ↦ by simpa [diagonal_mul,hu] using ha i⟩
  have hm : f m.val = f g := (hf.2 _ _).mp
    ⟨1,u,a,by simp,ha,hu,hz,by simp [m],ht,hv⟩
  have he : columnBorelSection (f g) = m := hm ▸ (columnBorelEquiv hf).left_inv m
  rw [he]
  apply (columnBorelEquiv hf).injective
  change f (columnBorelSection _).val = f (m*b).val
  rw [(hf.2 _ _).mp (columnBorelSection_params _)]
  obtain ⟨k',v,s,hk',hs,hv',hz',hm',ht',hu'⟩ := (hf.2 (m*b).val _).mpr rfl
  apply (hf.2 _ _).mp
  refine ⟨k*k',v,s,?_,hs,hv',hz',?_,ht',hu'⟩
  · simp only [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k.transpose, hk, one_mul, hk']
  · change g.val * b.val.val = _
    have e : m.val.val * b.val.val = _ := hm'
    rw [hg]
    simpa only [m, Matrix.mul_assoc] using congrArg (k * ·) e

open MeasureTheory in
theorem columnBorel_chart_rightInvariant {d : ℕ} {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) :
    ((groupHaar (d+1)).map (columnBorelSection ∘ f)).IsMulRightInvariant := by
  let : BorelSpace (SL (d+1)) := ⟨rfl⟩
  let := groupHaar_rightInvariant (d+1)
  have hm := (continuous_columnBorelSection d).measurable.comp hf.1
  constructor
  intro b
  have e : (· * b) ∘ (columnBorelSection ∘ f) =
      (columnBorelSection ∘ f) ∘ (· * b.val) :=
    funext fun g ↦ (columnBorelSection_mul hf g b).symm
  rw [Measure.map_map (measurable_mul_const b) hm, e,
    ← Measure.map_map hm (measurable_mul_const b.val), map_mul_right_eq_self]

#print axioms columnBorel_chart_rightInvariant
end SigabaNeo.Rogers
