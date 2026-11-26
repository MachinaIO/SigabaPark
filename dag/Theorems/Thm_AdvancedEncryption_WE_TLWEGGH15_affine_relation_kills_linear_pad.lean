import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

/-- **An affine relation among the gated rows kills every term that is linear in them, wide
error included.** Path values of the candidate have the form `m + L(c_z) + e_z`, where `c_z` is the
gated constraint row of path `z` and `L` is right multiplication by the leaf block
`Y = (I ⊗ S'_h) A_h + F`. The wide TLWE error `F` sits inside `L`, so an affine relation
`∑ α_z = 1`, `∑ α_z c_z = 0` removes pad and wide error together and leaves `m + ∑ α_z e_z`, with
only the inner-level (narrow) GGH15 noise `e_z`. So wide leaf errors are never independent per-path
noise and cannot close the overcomplete gap of `pq-we-masked-overcomplete-leaf`
(note `pq-we-tlwe-masked-ggh15-leaf`). -/
theorem AdvancedEncryption.WE.TLWEGGH15.affine_relation_kills_linear_pad {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] {ι : Type*} [Fintype ι] (L : V →ₗ[R] W) (c : ι → V) (α : ι → R)
    (hα : ∑ z, α z = 1) (hrel : ∑ z, α z • c z = 0) (m : W) (e : ι → W) :
    ∑ z, α z • (m + L (c z) + e z) = m + ∑ z, α z • e z
    := by sorry
