import Mathlib
open Polynomial Finset
open scoped BigOperators

theorem AdvancedEncryption.WE.BlindJoin.dual_kernel_card {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (E : V →ₗ[k] V) :
    Nat.card (LinearMap.ker E) = Nat.card (LinearMap.ker E.dualMap) := by sorry
