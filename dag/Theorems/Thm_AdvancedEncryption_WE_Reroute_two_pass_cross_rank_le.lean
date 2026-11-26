import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

open Matrix

/-- **Cross-partition rank of a two-pass evaluation is at most `t^3`.** Split the witness
variables into `X | Y`. In a two-pass layout every product of level matrices factors as
`u · P₁(x) Q₁(y) P₂(x) Q₂(y) · v` (pass 1 reads `X` then `Y`, pass 2 again). The `X × Y` matrix of
these values has rank at most `t^3`, `t` the matrix width. This is the count behind CVW18 §9.3.2
(`ρ = t^3` for `c = 2`; `t^{2c−1}` for `c` passes by the same factorization). When `2^{n/2} > t^3`
a balanced partition gives rank-deficient honest-zero matrices, and CVW18 Claim 9.8 distinguishes
functionally equivalent two-pass programs; so any proof of the reroute lemma must use a hypothesis
that fails for `c = 2` at large `n`, such as `2^{n/2} ≤ t^{2c−1}` (note
`pq-we-two-pass-reroute`, §6). -/
theorem AdvancedEncryption.WE.Reroute.two_pass_cross_rank_le {K X Y ι : Type*} [Field K] [Fintype X] [Fintype Y] [Fintype ι]
    [DecidableEq ι] (u v : ι → K) (P₁ P₂ : X → Matrix ι ι K) (Q₁ Q₂ : Y → Matrix ι ι K) :
    (Matrix.of fun x y => u ⬝ᵥ ((P₁ x * Q₁ y * P₂ x * Q₂ y) *ᵥ v)).rank
      ≤ Fintype.card ι ^ 3 := by sorry
