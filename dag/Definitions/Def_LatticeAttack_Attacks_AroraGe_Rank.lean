module

public import Definitions.Def_LatticeAttack_Attacks_AroraGe
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring
public import Mathlib.Data.ZMod.Basic

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

/-- For the legal one-dimensional instance with B = 1, s = 0 and every error zero,
the three factors correspond in order to errors -1, 0, 1. -/
theorem zeroErrorCubic {K : Type*} [CommRing K] (a x : K) :
    (-a * x + 1) * (-a * x) * (-a * x - 1) = a * x - a ^ 3 * x ^ 3 := by
  ring

/-- Coefficients of X, X² and X³ after moving the constant term to the RHS (zero). -/
def cubicRows {K ι : Type*} [CommRing K] (a : ι → K) : Matrix ι (Fin 3) K :=
  fun i ↦ ![a i, 0, -(a i ^ 3)]

theorem cubicRows_eval {K ι : Type*} [CommRing K] (a : ι → K) (x : K) (i : ι) :
    (cubicRows a).mulVec ![x, x ^ 2, x ^ 3] i =
      (-a i * x + 1) * (-a i * x) * (-a i * x - 1) := by
  rw [zeroErrorCubic]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cubicRows]
  ring

theorem cubicRows_not_injective {K ι : Type*} [CommRing K] [Nontrivial K] (a : ι → K) :
    ¬ Function.Injective (cubicRows a).mulVec := by
  intro h
  have hz : (cubicRows a).mulVec ![0, 1, 0] = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cubicRows]
  have he := h (hz.trans (Matrix.mulVec_zero _).symm)
  have := congrFun he (1 : Fin 3)
  simp at this

/-- Exact numerator of the full-rank probability on uniform m-by-1 matrices mod 5.
The statement holds at every sample size, including 3 plus arbitrary slack. -/
theorem fullRankCount_mod_five (m : ℕ) :
    (Finset.univ.filter (fun a : Fin m → ZMod 5 ↦
      Function.Injective (cubicRows a).mulVec)).card = 0 := by
  classical
  letI : Nontrivial (ZMod 5) := ⟨⟨0, 1, by decide⟩⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact cubicRows_not_injective a (Finset.mem_filter.mp ha).2

end SigabaNeo.Lattices.AroraGe

#print axioms SigabaNeo.Lattices.AroraGe.zeroErrorCubic
#print axioms SigabaNeo.Lattices.AroraGe.cubicRows_eval
#print axioms SigabaNeo.Lattices.AroraGe.cubicRows_not_injective
#print axioms SigabaNeo.Lattices.AroraGe.fullRankCount_mod_five
