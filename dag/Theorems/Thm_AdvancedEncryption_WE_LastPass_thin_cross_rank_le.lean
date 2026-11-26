import Mathlib.LinearAlgebra.Matrix.Rank

/-- **Thin first copies collapse the cross-partition rank.** If a matrix over a variable partition
`X | Y` has entries `Z[x, y] = ∑_{k<K} f_k(x) g_k(y) · ∑_{i<t} a_k(x)_i b_k(y)_i`, its rank is at
most `K·t`. This is the zero-evaluation matrix of a two-pass masked GGH15 whose first-copy
constraint secrets are bit-independent: the first copy then contributes only the clause
indicators `f_k(x) g_k(y)` (`K` clauses), and the last copy a single-pass product of dimension
`t`. Compare `t^3` for twisted first copies (`AdvancedEncryption.WE.Reroute.two_pass_cross_rank_le`,
open PR #61). -/
theorem AdvancedEncryption.WE.LastPass.thin_cross_rank_le {F : Type} [Field F] {X Y : Type}
    [Fintype X] [Fintype Y] (K t : ℕ) (f : Fin K → X → F) (g : Fin K → Y → F)
    (a : Fin K → X → Fin t → F) (b : Fin K → Y → Fin t → F) :
    (Matrix.of fun x y => ∑ k, f k x * g k y * ∑ i, a k x i * b k y i).rank ≤ K * t := by sorry
