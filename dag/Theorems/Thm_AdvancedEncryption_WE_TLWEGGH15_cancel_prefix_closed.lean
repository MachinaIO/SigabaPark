import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

/-- **A wide error at an inner level can only gate dead prefixes.** By the GGH15 path identity
(`AdvancedEncryption.WE.GGH15.path_identity`), the level-`j` error of path `z` enters the value read
with left matrix `J` as `J·(Ŝ_{0,z_0}⋯Ŝ_{j−1,z_{j−1}})·E_{j,z_j}·D_{>j}`. Since `D_{>j}` is a long
Gaussian product, a wide part `W` of `E_{j,b}` must cancel exactly, `J Ŝ_{<j,z} W_{j,z_j} = 0`, on
every valid path, or decryption fails. The cancellation depends only on `z_0, …, z_j`. So it also
holds on every path that shares its first `j + 1` bits with some valid path: a level-`j` wide
error can stay alive only on prefixes that no valid path extends. The encoder cannot know those
prefixes beyond the clauses already falsified inside the first `j + 1` variables, which is the
region where the cut lemma of `pq-we-masked-overcomplete-leaf` already gives an LWE proof
(note `pq-we-tlwe-masked-ggh15-leaf`). -/
theorem AdvancedEncryption.WE.TLWEGGH15.cancel_prefix_closed {R : Type*} [Ring R] {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ}
    (J : Matrix ν ι R) (S : Fin h → Bool → Matrix ι ι R) (W : Fin h → Bool → Matrix ι κ R)
    (j : Fin h) (valid : (Fin h → Bool) → Prop)
    (hvalid : ∀ z, valid z →
      J * ((List.ofFn fun i => S i (z i)).take j).prod * W j (z j) = 0)
    (z z' : Fin h → Bool) (hz' : valid z') (hpre : ∀ i : Fin h, i ≤ j → z i = z' i) :
    J * ((List.ofFn fun i => S i (z i)).take j).prod * W j (z j) = 0
    := by sorry
