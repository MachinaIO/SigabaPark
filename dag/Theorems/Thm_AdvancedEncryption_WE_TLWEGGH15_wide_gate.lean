import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

/-- **Clause-gated wide leaf error is gated by the whole path product.** In the masked
γ⊗-GGH15 candidate with a public trapdoor of the leaf matrix (note `pq-we-tlwe-masked-ggh15-leaf`),
the constraint rows of the leaf target are `(M_{h,b} ⊗ I)·((I ⊗ S'_{h,b}) A_h + F_{h,b})`, with a
wide (TLWE-width) error `F` placed only in the rows that the leaf plaintext `M_{h,b}` keeps. A path
reaches the leaf with the constraint coefficient `X ⊗ Y = (j_C M_{<h}) ⊗ (s'_0 S'_{<h})`. The
identity `(X ⊗ Y)((M ⊗ I) F) = ((X M) ⊗ Y) F` shows that the surviving wide error is
`((j_C M_z) ⊗ s'_0 S'_{<h}) F`: it vanishes on every path with `M_z = 0` (a witness), whatever
the prefix, and it is the same linear image of the gated row as the pad. -/
theorem AdvancedEncryption.WE.TLWEGGH15.wide_gate {R : Type*} [CommRing R] {ι κ ν μ : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    {ι' : Type*} (X : Matrix ι κ R) (Y : Matrix ι' ν R) (M : Matrix κ κ R)
    (F : Matrix (κ × ν) μ R) :
    (X ⊗ₖ Y) * ((M ⊗ₖ (1 : Matrix ν ν R)) * F) = ((X * M) ⊗ₖ Y) * F
    := by sorry
