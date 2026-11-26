import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Common

theorem solution {V S : Type*} [Fintype V] [DecidableEq S]
    (κ κ' : V → S) (N : ℕ)
    (hmono : ∀ T : Finset V, N ≤ T.card →
      ((∃ s, ∀ x ∈ T, κ x = s) ↔ (∃ s, ∀ x ∈ T, κ' x = s)))
    (x : V) (hx : N ≤ (Finset.univ.filter fun y => κ y = κ x).card) :
    (Finset.univ.filter fun y => κ y = κ x) = Finset.univ.filter fun y => κ' y = κ' x := by
  set c := Finset.univ.filter fun y => κ y = κ x with hc
  set c' := Finset.univ.filter fun y => κ' y = κ' x with hc'
  have hxc : x ∈ c := by simp [hc]
  have h1 : c ⊆ c' := by
    obtain ⟨s, hs⟩ := (hmono c hx).mp ⟨κ x, fun y hy => by simpa [hc] using hy⟩
    intro y hy
    simp [hc', hs y hy, hs x hxc]
  have hx' : N ≤ c'.card := hx.trans (Finset.card_le_card h1)
  have h2 : c' ⊆ c := by
    obtain ⟨s, hs⟩ := (hmono c' hx').mpr ⟨κ' x, fun y hy => by simpa [hc'] using hy⟩
    intro y hy
    simp [hc, hs y hy, hs x (h1 hxc)]
  exact Finset.Subset.antisymm h1 h2
