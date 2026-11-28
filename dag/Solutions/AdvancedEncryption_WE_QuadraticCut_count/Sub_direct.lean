import Definitions.Def_QuadraticNandCut
open AffineNandCut
open scoped BigOperators
theorem solution {X : Type*} [Fintype X] (qs : List (X→Bool)) :
    ((chars qs).map (fun t => ∑ x,t x)).sum =
    2^qs.length * ∑ x : X, if qs.all (fun q => !(q x)) then (1:ℤ) else 0 := by
  rw [interchange,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [orth]; split <;> simp
