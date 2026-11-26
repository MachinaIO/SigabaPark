import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Common

open Matrix

/-- **Kilian re-randomization preserves the relation space of the prefix rows.** If the joint
rows of the prefixes at a cut in two hybrids are related by one invertible matrix `T`
(`XB x = XA x · T`, the Kilian / basis-change form of a statistical re-randomization of the level
secrets), then a linear relation among the rows of one hybrid holds iff it holds in the other.
Idea (1) of note `pq-we-two-pass-reroute` (§3): a reroute changes which prefix rows coincide in
the comparator block, so no such `T` exists. -/
theorem AdvancedEncryption.WE.Reroute.kilian_relations_iff {K V ι : Type*} [Field K] [Fintype V] [Fintype ι] [DecidableEq ι]
    (XA XB : V → ι → K) (T : Matrix ι ι K) (hT : IsUnit T.det)
    (h : ∀ x, XB x = XA x ᵥ* T) (c : V → K) :
    (∑ x, c x • XA x = 0) ↔ (∑ x, c x • XB x = 0) := by sorry
