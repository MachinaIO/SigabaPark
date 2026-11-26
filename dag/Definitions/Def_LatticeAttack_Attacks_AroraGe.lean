module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Matrix.Mul

set_option autoImplicit true

public section

namespace SigabaNeo.Lattices.AroraGe

/-- Each sample whose integer error lies in the interval annihilates the product. -/
theorem boundedErrorEquation {K : Type*} [CommRing K] (B e : ℤ) (b prediction : K)
    (lo : -B ≤ e) (hi : e ≤ B) (sample : b - prediction = (e : K)) :
    ∏ j ∈ Finset.Icc (-B) B, (b - prediction - (j : K)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨lo, hi⟩)
  rw [sample, sub_self]

/-- In a homogeneous linearization retaining the constant monomial, any evaluation
vector satisfying all rows witnesses failure of injectivity. -/
theorem homogeneous_not_injective {K row col : Type*} [CommRing K] [Nontrivial K] [Fintype col]
    (M : Matrix row col K) (v : col → K) (constant : col) (hc : v constant = 1)
    (rows : M.mulVec v = 0) : ¬ Function.Injective M.mulVec := by
  intro inj
  have hv : v = 0 := inj (rows.trans (Matrix.mulVec_zero M).symm)
  simp [hv] at hc

end SigabaNeo.Lattices.AroraGe
