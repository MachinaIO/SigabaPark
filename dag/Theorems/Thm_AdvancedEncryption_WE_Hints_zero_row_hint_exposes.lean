import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **A preimage hint with a small target on a row exposes LWE samples along that row.** Let
`X` be a hint (a short preimage) under a matrix `H`, with target `Y = H X`, and let the row
combination `c` of the target be `f = c Y` (small, or zero). Then every LWE-type sample
`σ (c H) + e` along the row `δ = c H` maps under the hint to `σ f + e X`, which is small whenever
`f` is: the hint decodes the direction `δ`. In the masked-leak lemma `ML_i` of note
`pq-we-two-pass-reroute` the hidden row `δ` has small targets `f_b` under both children `D_b`, so
the leak can only be hidden by a pad; a hinted assumption whose challenge lies on such a row is
false (note `pq-we-hinted-lattice-assumptions`, §2). -/
theorem AdvancedEncryption.WE.Hints.zero_row_hint_exposes {R ι μ ν : Type*} [CommRing R]
    [Fintype ι] [Fintype μ] (H : Matrix ι μ R) (X : Matrix μ ν R) (c : ι → R) (f : ν → R)
    (hf : c ᵥ* (H * X) = f) (σ : R) (e : μ → R) :
    (σ • (c ᵥ* H) + e) ᵥ* X = σ • f + e ᵥ* X := by sorry
