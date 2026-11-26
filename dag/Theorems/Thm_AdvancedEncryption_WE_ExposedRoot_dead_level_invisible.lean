import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common

/-- **Dead levels are invisible (note `pq-we-exposed-root-reachable-lemma`, §4).** Let `P i` be
the set of parts, in the columns of slot `d`, of the rows reachable at level `i`. A reachable row
at level `i+1` is a combination of `v Ŝ_{i+1,0}` and `v Ŝ_{i+1,1}`, whose `d`-part is
`u_0 (m_{i+1,0} S_{i+1,0}) + u_1 (m_{i+1,1} S_{i+1,1})`. If slot `d` has both entries `0` at level
`j` (`N0 j = N1 j = 0`), then its part is `0` at every level after `j`. So the rows of `d`
after its dead level are unreachable from the exposed root row, CVW18 Lemma 4.4 applies to them
directly, and the entries of `d` after its dead level can be reset. -/
theorem AdvancedEncryption.WE.ExposedRoot.dead_level_invisible {R : Type*} [Ring R] {a n : Type*} [Fintype n]
    (P : ℕ → Set (Matrix a n R)) (N0 N1 : ℕ → Matrix n n R)
    (hstep : ∀ i v, v ∈ P (i + 1) → ∃ u0 ∈ P i, ∃ u1 ∈ P i, v = u0 * N0 i + u1 * N1 i)
    (j : ℕ) (hdead0 : N0 j = 0) (hdead1 : N1 j = 0) :
    ∀ i, j < i → ∀ v ∈ P i, v = 0 := by sorry
