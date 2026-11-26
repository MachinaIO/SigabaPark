import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Common

open Matrix

/-- **Pad reuse (note `pq-we-point-insertion-frontier`, §3).** A clause block's level-`L` target `U` is read by every prefix on which the clause is alive, with coefficient row `c x = w s S_x`. If the reading row of the target prefix `π` lies in the span of the other readers' rows (as soon as more than `n'` generic prefixes read it), then `c π · U` is that combination of the other readings, so `U` is not a one-time pad for `π` alone. -/
theorem AdvancedEncryption.WE.PointInsert.pad_reuse_span {R ι μ ν : Type*} [CommRing R] [Fintype μ] (c : ι → μ → R)
    (U : Matrix μ ν R) (π : ι) (s : Finset ι) (lam : ι → R)
    (h : c π = ∑ x ∈ s, lam x • c x) :
    c π ᵥ* U = ∑ x ∈ s, lam x • (c x ᵥ* U) := by sorry
