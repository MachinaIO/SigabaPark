import Definitions.Def_LatticeAttack_Reduction_Rogers_RogersOrderKDiagram
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

set_option autoImplicit true

noncomputable section
namespace SigabaNeo.Rogers

/-- The row coefficients of an integral pivot frame must belong to the kernel. -/
def diagramResidue {r k q} (A : Diagram r k (q+1)) : (Fin r → ℤ) →+ (Fin k → ZMod (q+1)) where
  toFun v := ∑ i, v i • (fun j ↦ (A.entry i j : ZMod (q+1)))
  map_zero' := by simp
  map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]

theorem diagramResidue_range {r k q} (A : Diagram r k (q+1)) :
    (diagramResidue A).range = rowImage A := by
  classical
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    change (∑ i, v i • (fun j ↦ (A.entry i j : ZMod (q+1)))) ∈ rowImage A
    exact (rowImage A).sum_mem fun i _ ↦ (rowImage A).zsmul_mem
      (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨Pi.single i 1, by simp [diagramResidue, Pi.single_apply]⟩

theorem diagramResidue_index {r k q} (A : Diagram r k (q+1)) :
    (diagramResidue A).ker.index = Nat.card (rowImage A) := by
  rw [AddSubgroup.index_ker, diagramResidue_range]

def diagramKernelBasis {r k q} (A : Diagram r k (q+1)) :
    Module.Basis (Fin r) ℤ (diagramResidue A).ker := by
  letI : (diagramResidue A).ker.FiniteIndex := ⟨by rw [diagramResidue_index]; exact Nat.card_pos.ne'⟩
  apply Module.finBasisOfFinrankEq
  rw [AddSubgroup.finrank_eq_of_finiteIndex]
  simp

theorem diagramKernelBasis_det {r k q} (A : Diagram r k (q+1)) :
    ((Pi.basisFun ℤ (Fin r)).det (fun i ↦ (diagramKernelBasis A i).val)).natAbs =
      Nat.card (rowImage A) := by
  rw [← diagramResidue_index]
  exact (AddSubgroup.index_eq_natAbs_det _ _ (diagramKernelBasis A)).symm

end SigabaNeo.Rogers
