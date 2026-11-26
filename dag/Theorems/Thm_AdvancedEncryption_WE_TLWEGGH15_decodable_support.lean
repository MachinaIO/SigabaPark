import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

open Matrix
open scoped Kronecker

/-- **Decodable combinations are supported on valid paths when the gated prefix rows are
independent.** Fix the last bit `b`. For clause `k` and prefix `i`, `v k i = s'_{0,k} S'_{<h,i}` is the
hidden prefix row, `bad k i` says that the path `(i, b)` falsifies clause `k`, and `L k` is right
multiplication by the wide leaf error `F_{k,b}` (injective when `F_{k,b}` has full row rank). A
combination `∑ α_i y_{(i,b)}` of path values is decodable with the public leaf trapdoor only if its
wide part `∑_i [bad k i] α_i v k i F_{k,b}` vanishes for every `k`. If each family `v k` is linearly
independent over `Z_q` (the case `h = 2`, `n' ≥ 2`, and generally `2^{h−1} ≤ n'`), then every
path that falsifies some clause has coefficient `0`: on a false statement nothing non-trivial
decodes (note `pq-we-tlwe-masked-ggh15-leaf`). -/
theorem AdvancedEncryption.WE.TLWEGGH15.decodable_support {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] {ι κ : Type*} [Fintype ι] (v : κ → ι → V)
    (hv : ∀ k, LinearIndependent K (v k)) (L : κ → V →ₗ[K] W)
    (hL : ∀ k, Function.Injective (L k)) (bad : κ → ι → Prop) [∀ k i, Decidable (bad k i)]
    (α : ι → K) (h : ∀ k, L k (∑ i, (if bad k i then α i else 0) • v k i) = 0) :
    ∀ k i, bad k i → α i = 0
    := by sorry
