import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnQRHaarUniqueness
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit true

open MeasureTheory Finset
open scoped ENNReal
namespace SigabaNeo.Rogers

private theorem crossing_card {d : ℕ} (k : Fin d) :
    (univ.filter (fun p : UpperEntry (d+1) ↦ p.val.1 ≤ k.castSucc ∧ k.castSucc < p.val.2)).card =
      (k.val + 1) * (d-k.val) := by
  classical
  let s := Iic k.castSucc ×ˢ Ioi k.castSucc
  have hs : s.card = _ := card_product (Iic k.castSucc) (Ioi k.castSucc)
  rw [Fin.card_Iic,Fin.card_Ioi] at hs
  convert_to _ = s.card
  · simpa using hs.symm
  apply card_bij (fun p _ ↦ p.val)
  · intro p hp
    simpa [s] using (mem_filter.mp hp).2
  · exact fun _ _ _ _ h ↦ Subtype.ext h
  · intro p hp
    have h : p.1 ≤ k.castSucc ∧ k.castSucc < p.2 := by simpa [s] using hp
    exact ⟨⟨p,h.1.trans_lt h.2⟩, mem_filter.mpr ⟨mem_univ _,h⟩,rfl⟩

theorem sum_column_log_ratios {d : ℕ} (x : Fin (d+1) → ℝ) :
    ∑ p : UpperEntry (d+1), (x p.val.2 - x p.val.1) =
    ∑ k : Fin d, ((k.val + 1 : ℕ) * ((d-k.val : ℕ) : ℝ)) *
      (x k.succ - x k.castSucc) := by
  classical
  let Δ (k : Fin d) := x k.succ - x k.castSucc
  let crosses (p : UpperEntry (d+1)) (k : Fin d) :=
    p.val.1 ≤ k.castSucc ∧ k.castSucc < p.val.2
  have pair (p : UpperEntry (d+1)) : x p.val.2 - x p.val.1 =
      ∑ k : Fin d, if crosses p k then Δ k else 0 := by
    let i : Fin d := ⟨p.val.1.val, by have := p.property; omega⟩
    let j : Fin d := ⟨p.val.2.val-1, by omega⟩
    have h : i ≤ j := by have := p.property; change p.val.1.val ≤ p.val.2.val - 1; omega
    have hj : j.succ = p.val.2 := by apply Fin.ext; have := p.property; dsimp [j]; omega
    calc x p.val.2 - x p.val.1 = x j.succ - x i.castSucc := by rw [hj]; rfl
         _ = ∑ k ∈ Icc i j, Δ k := (Fin.sum_Icc_sub h x).symm
         _ = _ := ?_
    rw [← sum_filter]
    congr 1
    ext k
    simp [crosses,i,j,Fin.le_def,Fin.lt_def]
    omega
  simp_rw [pair]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [← sum_filter, sum_const, nsmul_eq_mul, show (univ.filter fun p ↦ crosses p k).card =
    _ from crossing_card k, Nat.cast_mul]

private theorem columnWeight_shift {d : ℕ} (s : Fin (d+1) → ℝ) (hs : ∀ i, 0 < s i)
    (t : Fin d → ℝ) :
    columnRootWeight d t = ENNReal.ofReal (∏ p : UpperEntry (d+1), s p.val.2 / s p.val.1) *
      columnRootWeight d (fun k ↦ t k + (Real.log (s k.succ) - Real.log (s k.castSucc))) := by
  unfold columnRootWeight
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg (fun _ _ ↦ div_nonneg (hs _).le (hs _).le))]
  congr 1
  have he (p : UpperEntry (d+1)) :
      s p.val.2 / s p.val.1 = Real.exp (Real.log (s p.val.2) - Real.log (s p.val.1)) := by
    simp [Real.exp_sub, Real.exp_log (hs _)]
  simp_rw [he]
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add,
    sum_column_log_ratios (fun i ↦ Real.log (s i)), ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  ring

theorem columnRoot_shift_map {d : ℕ} (s : Fin (d+1) → ℝ) (hs : ∀ i, 0 < s i) :
    (columnRootMeasure d).map
      (fun t k ↦ t k + (Real.log (s k.succ) - Real.log (s k.castSucc))) =
      ENNReal.ofReal (∏ p : UpperEntry (d+1), s p.val.2 / s p.val.1) • columnRootMeasure d := by
  let v := fun k : Fin d ↦ Real.log (s k.succ) - Real.log (s k.castSucc)
  let c := ENNReal.ofReal (∏ p : UpperEntry (d+1), s p.val.2 / s p.val.1)
  let w := columnRootWeight d
  have hw : Measurable w := by unfold w columnRootWeight; fun_prop
  change (Measure.map (· + v) ((volume : Measure (Fin d → ℝ)).withDensity w)) =
    c • volume.withDensity w
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_add_const v), lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hw (show Measurable (fun a ↦ F (a + v)) from hF.comp (measurable_add_const v)),
    lintegral_withDensity_eq_lintegral_mul _ hw hF]
  have h (t : Fin d → ℝ) : w t * F (t + v) = c * ((w * F) (t + v)) := by
    rw [show w t = c * w (t + v) from columnWeight_shift s hs t]
    exact mul_assoc _ _ _
  simp only [Pi.mul_apply] at *
  simp_rw [h]
  rw [lintegral_const_mul c (show Measurable (fun a ↦ w (a+v) * F (a+v)) from
    (hw.mul hF).comp (measurable_add_const v))]
  exact congrArg (c * ·) ((measurePreserving_add_right volume v).lintegral_comp (hw.mul hF))

end SigabaNeo.Rogers
