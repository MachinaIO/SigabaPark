import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Common

/-- **Small classes force many classes.** If every class of `κ : V → S` has at most `b`
members, then `|V| ≤ b · |S|`. Combined with `class_flip_bound`, the number of automaton states at
a rank-testable cut `i` is at least `2^i / max(N, f)` (note `pq-we-shallow-split-arrangements`). -/
theorem AdvancedEncryption.WE.ShallowSplit.small_classes_card {V S : Type*} [Fintype V] [Fintype S] [DecidableEq S]
    (κ : V → S) (b : ℕ)
    (hb : ∀ x, (Finset.univ.filter fun y => κ y = κ x).card ≤ b) :
    Fintype.card V ≤ b * Fintype.card S := by sorry
