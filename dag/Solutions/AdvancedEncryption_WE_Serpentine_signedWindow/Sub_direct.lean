import Definitions.Def_SerpentineBankMachine
open SerpentineLaws SerpentineRing SigabaNeo.Lattices.Algo Cslib
theorem solution {n : Nat} (k a : Negacyclic (ZMod (2^4)) n) (j : Nat) (hj : j<n) :
    (k*a).coeffs ⟨j,hj⟩ =
      ∑ i ∈ Finset.range n, keyAt n (coefOf k) (n+j-i)*coefOf a i := by
  rw [coeffs_mul_eq_sum k a j hj]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  by_cases h : i≤j
  · simp [negaTerm,keyAt,h,show ¬n+j-i<n by omega,show n+j-i-n=j-i by omega]
  · simp [negaTerm,keyAt,h,show n+j-i<n by omega]
