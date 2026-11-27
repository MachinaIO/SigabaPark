import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnBorelUniqueness
import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnRootJacobian

set_option autoImplicit true

noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace SigabaNeo.Rogers

private theorem logs_add {d : ℕ} (x y : Fin d → ℝ) (i : Fin (d+1)) :
    columnDiagLogs (x+y) i = columnDiagLogs x i + columnDiagLogs y i := by
  have h (j : Fin (d+1)) : Fin.partialSum (x+y) j = Fin.partialSum x j + Fin.partialSum y j := by
    induction j using Fin.induction with
    | zero => simp
    | succ k ih => simp [Fin.partialSum_succ, ih]; ring
  simp [columnDiagLogs, h, Finset.sum_add_distrib]
  ring

private def diagScale {n : ℕ} (s : Fin n → ℝ) (v : UpperEntry n → ℝ) :=
  fun i : UpperEntry n ↦ v i * s i.val.2 / s i.val.1

private def affineUpper {n : ℕ} (v u : UpperEntry n → ℝ) :=
  v + (upperRightLinear (columnUpperMatrix v)).toLin' u

private theorem upper_mul_eq {n : ℕ} (u v : UpperEntry n → ℝ) :
    columnUpperMatrix (affineUpper v u) = columnUpperMatrix u * columnUpperMatrix v := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · have e := upperRightAffine_apply (columnUpperMatrix u) (columnUpperMatrix v)
      (by simp [columnUpperMatrix]) (fun i j h ↦ columnUpperMatrix_tri _ h) ⟨(i,j),h⟩
    have eu : (fun j : UpperEntry n ↦ columnUpperMatrix u j.val.1 j.val.2) = u :=
      funext fun j ↦ dite_eq_left j.property
    rw [eu] at e
    simpa [columnUpperMatrix,affineUpper,h, Subtype.property] using e.symm
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [columnUpperMatrix]
    · intro j _ he
      rcases lt_or_gt_of_ne he with h | h
      · simp [columnUpperMatrix_tri u h]
      · simp [columnUpperMatrix_tri v h]
    · simp
  · rw [(columnUpperMatrix_tri u).mul (columnUpperMatrix_tri v) h, columnUpperMatrix_tri _ h]

private theorem section_product {d : ℕ} (p q : ColumnParameters d) :
    let s := fun i ↦ Real.exp (columnDiagLogs q.1 i)
    columnBorelSection (p.1 + q.1, affineUpper q.2 (diagScale s p.2)) =
      columnBorelSection p * columnBorelSection q := by
  dsimp only
  apply Subtype.ext
  apply Subtype.ext
  change diagonal _ * columnUpperMatrix _ =
    (diagonal _ * columnUpperMatrix _) * (diagonal _ * columnUpperMatrix _)
  rw [upper_mul_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (diagonal _)]
  congr 1
  ext i j
  simp only [diagonal_mul, mul_diagonal, diagonal_mul, logs_add, Real.exp_add]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [columnUpperMatrix, h, diagScale]
    field_simp
  · simp [columnUpperMatrix]
  · simp [columnUpperMatrix,h.not_gt,h.ne']

theorem columnBorel_candidate_rightInvariant (d : ℕ) :
    (((columnRootMeasure d).prod volume).map columnBorelSection).IsMulRightInvariant := by
  let : BorelSpace (SL (d+1)) := ⟨rfl⟩
  constructor
  intro b
  obtain ⟨q,rfl⟩ := columnBorelSection_surjective d b
  let s (i : Fin (d+1)) := Real.exp (columnDiagLogs q.1 i)
  let D := ∏ i : UpperEntry (d+1), s i.val.2 / s i.val.1
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hs : Measurable (diagScale s) := by unfold diagScale; fun_prop
  have ha : Measurable (affineUpper q.2) :=
    measurable_const.add (LinearMap.continuous_of_finiteDimensional _).measurable
  have hr := columnRoot_shift_map s (fun _ ↦ Real.exp_pos _)
  have he (k : Fin d) : Real.log (s k.succ) - Real.log (s k.castSucc) = q.1 k := by
    simp [s,columnDiagLogs_diff]
  simp_rw [he] at hr
  have hu := upperRightAffine_map_volume (columnUpperMatrix q.2) (by simp [columnUpperMatrix])
    (fun i j h ↦ columnUpperMatrix_tri _ h)
  have eq : (fun i : UpperEntry (d+1) ↦ columnUpperMatrix q.2 i.val.1 i.val.2) = q.2 :=
    funext fun i ↦ dite_eq_left i.property
  rw [eq] at hu
  change Measure.map (affineUpper q.2) volume = volume at hu
  let T := Prod.map (fun t : Fin d → ℝ ↦ t + q.1) (affineUpper q.2 ∘ diagScale s)
  have hT : Measurable T := (measurable_add_const q.1).prodMap (ha.comp hs)
  have hinv : Measure.map T ((columnRootMeasure d).prod volume) = (columnRootMeasure d).prod volume := by
    rw [show T = _ from rfl, ← Measure.map_prod_map _ _ (measurable_add_const _) (ha.comp hs),
      ← Measure.map_map ha hs]
    change ((columnRootMeasure d).map (fun t k ↦ t k + q.1 k)).prod
      ((volume.map (diagScale s)).map (affineUpper q.2)) = _
    rw [hr, show volume.map (diagScale s) = ENNReal.ofReal D⁻¹ • volume from
      upperDiagonal_map_volume s (fun _ ↦ Real.exp_pos _), Measure.map_smul _ ha.aemeasurable, hu,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    rw [← ENNReal.ofReal_mul hD.le, mul_inv_cancel₀ hD.ne', ENNReal.ofReal_one, one_smul]
  have hsec := (continuous_columnBorelSection d).measurable
  have hc : (· * columnBorelSection q) ∘ columnBorelSection = columnBorelSection ∘ T :=
    funext fun p ↦ (section_product p q).symm
  rw [Measure.map_map (measurable_mul_const _) hsec, hc, ← Measure.map_map hsec hT, hinv]

theorem columnQRHaarPushforward {d : ℕ} (hd : 1 ≤ d) {f : SL (d+1) → ColumnParameters d}
    (hf : IsColumnChart f) :
    ∃ C : ℝ, (groupHaar (d+1)).map f = ENNReal.ofReal C • (columnRootMeasure d).prod volume :=
  columnLaw_of_borel_candidate hd hf (columnBorel_candidate_rightInvariant d)

#print axioms columnQRHaarPushforward
end SigabaNeo.Rogers
