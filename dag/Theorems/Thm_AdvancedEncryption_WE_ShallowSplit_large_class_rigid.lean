import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Common

/-- **Rank tests pin the large classes.** Two colorings `κ, κ'` of the prefixes at a cut (the
automaton states of two hybrids) such that every set of at least `N` prefixes is monochromatic
under `κ` iff it is monochromatic under `κ'` (what the rank test of a GGH15 encoding with
state-determined rows sees, `N ≈` noise dimension plus width) have the same classes of size
`≥ N`. So a statement-independent hop can never move a prefix into or out of a large class (note
`pq-we-shallow-split-arrangements`). -/
theorem AdvancedEncryption.WE.ShallowSplit.large_class_rigid {V S : Type*} [Fintype V] [DecidableEq S]
    (κ κ' : V → S) (N : ℕ)
    (hmono : ∀ T : Finset V, N ≤ T.card →
      ((∃ s, ∀ x ∈ T, κ x = s) ↔ (∃ s, ∀ x ∈ T, κ' x = s)))
    (x : V) (hx : N ≤ (Finset.univ.filter fun y => κ y = κ x).card) :
    (Finset.univ.filter fun y => κ y = κ x) = Finset.univ.filter fun y => κ' y = κ' x := by sorry
