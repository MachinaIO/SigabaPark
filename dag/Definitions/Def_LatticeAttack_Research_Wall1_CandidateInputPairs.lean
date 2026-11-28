import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option autoImplicit true

/-! # Ordered candidate pairs partitioned by their input

The square sum includes diagonal pairs. Subtracting it from the full product
therefore counts exactly the ordered pairs with different inputs.
-/

namespace SigabaNeo.Wall1.CandidateInputPairs
open Finset

variable {α β : Type*} [DecidableEq β]

/-- Sum of squared input-fiber sizes in a finite candidate family. -/
def inputSquareSum (T : Finset α) (f : α → β) : ℕ :=
  ∑ s ∈ T.image f, ((T.filter fun z ↦ f z = s).card)^2

/-- Ordered pairs with the same input, including the diagonal, are fiber squares. -/
theorem same_input_pairs_card (T : Finset α) (f : α → β) :
    ((T ×ˢ T).filter fun p ↦ f p.1 = f p.2).card = inputSquareSum T f := by
  let S := (T ×ˢ T).filter fun p ↦ f p.1 = f p.2
  have hmap : (S : Set (α × α)).MapsTo (fun p ↦ f p.1) (T.image f) := by
    intro p hp
    exact mem_image_of_mem f (mem_product.mp (mem_filter.mp hp).1).1
  change S.card = _
  rw [card_eq_sum_card_fiberwise hmap]
  unfold inputSquareSum
  apply sum_congr rfl
  intro s hs
  have hfiber : (S.filter fun p ↦ f p.1 = s) =
      (T.filter fun z ↦ f z = s) ×ˢ (T.filter fun z ↦ f z = s) := by
    ext p
    simp only [S, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, he⟩, hfa⟩
      exact ⟨⟨ha, hfa⟩, ⟨hb, he.symm.trans hfa⟩⟩
    · rintro ⟨⟨ha, hfa⟩, ⟨hb, hfb⟩⟩
      exact ⟨⟨⟨ha, hb⟩, hfa.trans hfb.symm⟩, hfa⟩
  rw [hfiber, card_product, pow_two]

/-- The square sum is at most the full product size, so the subtraction does not truncate. -/
theorem inputSquareSum_le_card_sq (T : Finset α) (f : α → β) :
    inputSquareSum T f ≤ T.card^2 := by
  rw [← same_input_pairs_card]
  simpa only [card_product, pow_two] using
    (card_filter_le (s := T ×ˢ T) (p := fun p ↦ f p.1 = f p.2))

/-- Exact number of ordered pairs with distinct inputs. -/
theorem different_input_pairs_card (T : Finset α) (f : α → β) :
    ((T ×ˢ T).filter fun p ↦ f p.1 ≠ f p.2).card =
      T.card^2 - inputSquareSum T f := by
  have hp := card_filter_add_card_filter_not (s := T ×ˢ T)
    (p := fun p ↦ f p.1 = f p.2)
  rw [same_input_pairs_card, card_product] at hp
  rw [pow_two]
  apply Nat.eq_sub_of_add_eq
  simpa only [add_comm] using hp

end SigabaNeo.Wall1.CandidateInputPairs

#print axioms SigabaNeo.Wall1.CandidateInputPairs.same_input_pairs_card
#print axioms SigabaNeo.Wall1.CandidateInputPairs.inputSquareSum_le_card_sq
#print axioms SigabaNeo.Wall1.CandidateInputPairs.different_input_pairs_card
