module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe_Rank

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

/-- Nonconstant coefficients for the one-variable cubic with shifted secret and zero error. -/
def shiftedCubicRows {K ι : Type*} [CommRing K] (a : ι → K) (s : K) : Matrix ι (Fin 3) K :=
  fun i ↦ ![a i - 3 * a i ^ 3 * s ^ 2, 3 * a i ^ 3 * s, -(a i ^ 3)]

theorem shiftedCubicRows_eval {K ι : Type*} [CommRing K] (a : ι → K) (s x : K) (i : ι) :
    (shiftedCubicRows a s).mulVec ![x, x ^ 2, x ^ 3] i + ((a i * s) ^ 3 - a i * s) =
      (a i * (s - x) + 1) * (a i * (s - x)) * (a i * (s - x) - 1) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, shiftedCubicRows]
  ring

theorem shiftedCubicRows_not_injective {K ι : Type*} [CommRing K] [Nontrivial K]
    (a : ι → K) (s : K) : ¬ Function.Injective (shiftedCubicRows a s).mulVec := by
  intro h
  have hz : (shiftedCubicRows a s).mulVec ![0, 1, 3 * s] = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, shiftedCubicRows]
    ring
  have he := h (hz.trans (Matrix.mulVec_zero _).symm)
  have := congrFun he (1 : Fin 3)
  simp at this

open Classical in
/-- Exact full-rank count over both the sample matrix and the shifted secret. -/
theorem shiftedFullRankCount {K : Type*} [Field K] [Fintype K] (m : ℕ) :
    (Finset.univ.filter (fun p : (Fin m → K) × K ↦
      Function.Injective (shiftedCubicRows p.1 p.2).mulVec)).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  exact Finset.eq_empty_iff_forall_notMem.mpr fun p hp ↦
    shiftedCubicRows_not_injective p.1 p.2 (Finset.mem_filter.mp hp).2

end SigabaNeo.Lattices.AroraGe

#print axioms SigabaNeo.Lattices.AroraGe.shiftedCubicRows_eval
#print axioms SigabaNeo.Lattices.AroraGe.shiftedCubicRows_not_injective
#print axioms SigabaNeo.Lattices.AroraGe.shiftedFullRankCount
