import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open scoped BigOperators

theorem solution (T need : ℕ) :
    ((Finset.univ : Finset (Fin T)).powerset.filter (fun x => x.card < need)).card =
      ∑ i ∈ Finset.range need, T.choose i := by
  classical
  let u : Finset (Fin T) := Finset.univ
  have he : u.powerset.filter (fun x => x.card < need) =
      (Finset.range need).biUnion (fun i => u.powersetCard i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨x.card, h, hx, rfl⟩
    · rintro ⟨i, hi, hx, rfl⟩
      exact ⟨hx, hi⟩
  change (u.powerset.filter (fun x => x.card < need)).card = _
  rw [he, Finset.card_biUnion]
  · simp [u, Finset.card_powersetCard]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
