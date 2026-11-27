import Mathlib.LinearAlgebra.Lagrange
open Polynomial Finset
open scoped Polynomial
/-- A single family of public weights transports all bounded-degree energy readouts to zero. -/
theorem AdvancedEncryption.WE.OnceEnergy.moment_endpoint {K : Type*} [Field K] [DecidableEq K] (s : Finset K) (hs : s.Nonempty) :
    ∃ weights : K → K, (∑ i ∈ s, weights i) = 1 ∧
      ∀ f : K[X], f.degree < s.card → (∑ i ∈ s, f.eval i * weights i) = f.eval 0 := by sorry
