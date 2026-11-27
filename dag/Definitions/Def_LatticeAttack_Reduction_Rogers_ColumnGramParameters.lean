module

public import Definitions.Def_LatticeAttack_Reduction_Rogers_ColumnHaarCoordinates
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

set_option autoImplicit true

@[expose] public section
noncomputable section
open MeasureTheory InnerProductSpace
namespace SigabaNeo.Rogers

local instance (n : ℕ) : BorelSpace (SL n) := ⟨rfl⟩

def qrColumn {n : ℕ} (g : SL n) (i : Fin n) : E n :=
  WithLp.toLp 2 (fun j ↦ g.val j i)

def qrResidual {n : ℕ} (g : SL n) := gramSchmidt ℝ (qrColumn g)

def gramColumnParameters {d : ℕ} (g : SL (d+1)) : ColumnParameters d :=
  ((fun i ↦ Real.log ‖qrResidual g i.succ‖ - Real.log ‖qrResidual g i.castSucc‖),
   fun p ↦ inner ℝ (qrResidual g p.val.1) (qrColumn g p.val.2) / ‖qrResidual g p.val.1‖ ^ 2)

theorem measurable_qrColumn {n : ℕ} (i : Fin n) : Measurable (fun g : SL n ↦ qrColumn g i) := by
  apply Continuous.measurable
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun j ↦ (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)

theorem measurable_qrResidual {n : ℕ} (i : Fin n) :
    Measurable (fun g : SL n ↦ qrResidual g i) := by
  apply wellFounded_lt.induction i
  intro i ih
  have heq (g : SL n) := gramSchmidt_def'' ℝ (qrColumn g) i
  have hfun : (fun g : SL n ↦ qrResidual g i) = (fun g ↦ qrColumn g i -
      ∑ j ∈ Finset.Iio i, (inner ℝ (qrResidual g j) (qrColumn g i) /
        ‖qrResidual g j‖ ^ 2) • qrResidual g j) := by
    funext g
    exact eq_sub_of_add_eq (heq g).symm
  rw [hfun]
  apply (measurable_qrColumn i).sub
  apply Finset.measurable_fun_sum
  intro j hj
  have h := ih j (Finset.mem_Iio.mp hj)
  exact ((h.inner (measurable_qrColumn i)).div (h.norm.pow_const 2)).smul h

theorem measurable_gramColumnParameters (d : ℕ) : Measurable (@gramColumnParameters d) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval fun (i : Fin d) ↦ ((measurable_qrResidual i.succ).norm.log).sub
      ((measurable_qrResidual i.castSucc).norm.log)
  · exact Measurable.of_eval fun (p : UpperEntry (d+1)) ↦ ((measurable_qrResidual p.val.1).inner
      (measurable_qrColumn p.val.2)).div ((measurable_qrResidual p.val.1).norm.pow_const 2)

end SigabaNeo.Rogers
