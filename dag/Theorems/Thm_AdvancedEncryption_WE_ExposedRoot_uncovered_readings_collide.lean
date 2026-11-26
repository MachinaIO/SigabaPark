import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel

/-- **The standalone one-slot zero flip is false (note `pq-we-exposed-root-reachable-lemma`, §1).**
Smallest case: one mask block, one slot with program `[b = p_1]` at level 1, no cover. On the
zero child `b = 1 - p_1` the exposed row `Rv = A_0^{mask} + a_0` satisfies
`Rv D_{1,b} = R_1 A_1^{mask} + e_1` (the slot contributes only noise). The mask block is
bit-independent, so `A_1^{mask} D_{2,b'} = R_2 A_2^{mask} + E_{b'}` for both `b'`. Then the two
readings `Rv D_{1,b} D_{2,0}` and `Rv D_{1,b} D_{2,1}` differ by the short matrix below, while after
the flip they differ by `s (S_{b0} - S_{b1}) a_2`-type pseudorandom terms. So flipping a zero of a
slot whose departing strings are not padded by another slot is distinguishable: the (cover)
condition is necessary. -/
theorem AdvancedEncryption.WE.ExposedRoot.uncovered_readings_collide {R : Type*} [Ring R] {a b c d : Type*}
    [Fintype b] [Fintype c] [Fintype d]
    (Rv : Matrix a b R) (D1 : Matrix b c R) (R1 : Matrix a c R) (Am1 : Matrix c c R)
    (e1 : Matrix a c R)
    (D20 D21 : Matrix c d R) (R2 : Matrix c c R) (Am2 : Matrix c d R) (E0 E1 : Matrix c d R)
    (hR1 : Rv * D1 = R1 * Am1 + e1)
    (h0 : Am1 * D20 = R2 * Am2 + E0) (h1 : Am1 * D21 = R2 * Am2 + E1) :
    Rv * D1 * D20 - Rv * D1 * D21 = R1 * (E0 - E1) + e1 * (D20 - D21) := by sorry
