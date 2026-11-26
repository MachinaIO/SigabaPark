import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Common

/-- **A class that never splits can only be flipped all at once.** Labels `ℓ t x u` (does path
`x u` carry the replaced mask in hybrid `t`) go from all `false` to all `true`; at step `t` the
prefixes whose label at suffix `u` changes lie in a set `F t u` of size `≤ f`. If the prefixes of
`c` share their labels in every hybrid (they stay in one automaton state), then `|c| ≤ f`. With
`large_class_rigid` this bounds every class at a rank-testable cut (note
`pq-we-shallow-split-arrangements`). -/
theorem AdvancedEncryption.WE.ShallowSplit.class_flip_bound {V U : Type*}
    (ℓ : ℕ → V → U → Bool) (n f : ℕ) (F : ℕ → U → Finset V)
    (hF : ∀ t x u, ℓ (t + 1) x u ≠ ℓ t x u → x ∈ F t u) (hf : ∀ t u, (F t u).card ≤ f)
    (h0 : ∀ x u, ℓ 0 x u = false) (hn : ∀ x u, ℓ n x u = true)
    (c : Finset V) (hc : ∀ t x y, x ∈ c → y ∈ c → ℓ t x = ℓ t y) (u : U) :
    c.card ≤ f := by sorry
