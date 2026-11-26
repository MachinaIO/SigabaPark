import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Common

/-- **Re-reading removes honest rectangles.** At a cut of a layout, the honest (consistent)
string of witness `w` splits as `(pre w, suf w)`. In a two-pass layout that re-reads every
variable, the suffix at a first-pass cut (and the prefix at a later cut) determines `w`, so `suf`
(or `pre`) is injective. Then no rectangle `S × T` of honest strings at a single level cut has both
sides of size `≥ 2`, so the single-cut rank tests (CVW18 Claim 9.4, the PLR-hop rank obstruction)
have nothing to act on. Rank tests over a *variable* partition (CVW18 §9.3.2) remain; their
dimension grows exponentially in the number of passes (note `pq-we-multipass-ggh15`). -/
theorem AdvancedEncryption.WE.MultiPass.no_honest_rectangle {W V U : Type*} (pre : W → V) (suf : W → U)
    (hinj : Function.Injective pre ∨ Function.Injective suf)
    (S : Finset V) (T : Finset U)
    (hST : ∀ x ∈ S, ∀ u ∈ T, ∃ w, pre w = x ∧ suf w = u) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by sorry
