import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Common

open Matrix

/-- **A lossy matrix with a known kernel of its secret part has an approximate trapdoor.** If
`A = B C + F` (LWE lossy mode) and `C K = 0`, then `A K = F K`, which is short when `F` and `K`
are. A reduction that builds a lossy level matrix together with such a `K` holds a short
approximate kernel, just like the preimage of a zero child, so the self-defeat of
`Hints.zero_row_hint_exposes` applies to it (note `pq-we-zero-entry-crossing`, §3). -/
theorem AdvancedEncryption.WE.ZeroCross.lossy_kernel_approx_trapdoor {R ι κ μ ν : Type*} [CommRing R] [Fintype κ] [Fintype μ]
    (B : Matrix ι κ R) (C : Matrix κ μ R) (F : Matrix ι μ R) (K : Matrix μ ν R)
    (hC : C * K = 0) : (B * C + F) * K = F * K := by sorry
