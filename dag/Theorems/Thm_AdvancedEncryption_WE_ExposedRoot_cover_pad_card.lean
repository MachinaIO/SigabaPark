import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Common

/-- **Cover pad (note `pq-we-exposed-root-reachable-lemma`, §3).** In the co-located cover
flip, the changed term of the flipped slot `d` enters the view only as
`x + M u`, where `x` is the flipped slot's own contribution (`E` before, `S a + E` after the
flip), `M` is invertible (here `M = I`) and `u` is the fresh uniform level-`L` target of the
cover slot `c`.
Exactly one `u` gives each value, so the law of `x + M u` is uniform for every `x`, and the two
hybrids have the same law exactly. With `M = s · 1` it also shows that a full-cube slot masks the
exposed root row (§5). -/
theorem AdvancedEncryption.WE.ExposedRoot.cover_pad_card {R : Type*} [Ring R] [Fintype R] [DecidableEq R] {n k : Type*}
    [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (M Minv : Matrix n n R) (h1 : M * Minv = 1) (h2 : Minv * M = 1)
    (x t : Matrix n k R) :
    (Finset.univ.filter (fun u : Matrix n k R => x + M * u = t)).card = 1 := by sorry
