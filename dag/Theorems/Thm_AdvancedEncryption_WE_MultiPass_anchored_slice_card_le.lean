import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Common

/-- **Counting step of the anchored multi-pass bound.** Witnesses `w` fall into the classes
`cls w` of the frozen first pass (at most `#states` of them); `pref w` is the length-`c` prefix of
the second copy, with fibers of size `b = 2^(n-c)`; and within one class, a fixed cut admits at most
`D` distinct prefixes (fixed-cut lemma inside the slice). Then `2^n ≤ #states · b · D`, which with
`b ≤ D` (projection at second-pass depth `n - c`) gives `D^2 · #states ≥ 2^n` (note
`pq-we-multipass-ggh15`). -/
theorem AdvancedEncryption.WE.MultiPass.anchored_slice_card_le {Wit S Pre : Type*} [Fintype Wit] [DecidableEq S] [DecidableEq Pre]
    (cls : Wit → S) (states : Finset S) (hcls : ∀ w, cls w ∈ states)
    (pref : Wit → Pre) (b D : ℕ)
    (hfib : ∀ p, (Finset.univ.filter fun w => pref w = p).card ≤ b)
    (hD : ∀ s ∈ states, ((Finset.univ.filter fun w => cls w = s).image pref).card ≤ D) :
    Fintype.card Wit ≤ states.card * (b * D) := by sorry
