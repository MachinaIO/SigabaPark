import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common

/-- **Both eq chains of a reroute are redundant.** In reflected Gray order the paths below any
prefix have consecutive ranks (an order-convex set). Let `I` and `J` be the rank sets of the two
subtrees at the level `j` where the codewords of ranks `t` and `t + 1` first differ (`t ∈ I`,
`t + 1 ∈ J`). Then `I` lies entirely at ranks `≤ t` (every path below the old chain prefix is lt
at threshold `t + 1`) and `J` entirely at ranks `≥ t + 1` (every path below the new chain prefix
is eq/gt at threshold `t + 1`). So, once path `t` is relabelled `mask'` by ERASE, the old chain is
a redundant chain inside an lt subtree and the new chain a redundant chain inside a gt subtree:
the reroute is two collapses of redundant single-prefix chains onto a common automaton (note
`pq-we-two-pass-reroute`, §1). -/
theorem AdvancedEncryption.WE.Reroute.adjacent_chains_redundant (I J : Set ℕ)
    (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I)
    (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c, a ≤ c → c ≤ b → c ∈ J)
    (t : ℕ) (htI : t ∈ I) (ht1I : t + 1 ∉ I) (ht1J : t + 1 ∈ J) (htJ : t ∉ J) :
    (∀ y ∈ I, y ≤ t) ∧ (∀ y ∈ J, t + 1 ≤ y) := by sorry
