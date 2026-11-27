import Mathlib
open Polynomial Finset
open scoped BigOperators

theorem solution {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (E : V →ₗ[k] V) :
    Nat.card (LinearMap.ker E) = Nat.card (LinearMap.ker E.dualMap) := by
  classical
  rw [Module.natCard_eq_pow_finrank (K := k) (V := LinearMap.ker E),
      Module.natCard_eq_pow_finrank (K := k) (V := LinearMap.ker E.dualMap)]
  congr 1
  have h := E.finrank_range_add_finrank_ker
  have hd := E.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at hd
  exact Nat.add_left_cancel (h.trans hd.symm)

