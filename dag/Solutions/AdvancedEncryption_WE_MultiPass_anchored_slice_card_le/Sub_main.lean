import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Common

theorem solution {Wit S Pre : Type*} [Fintype Wit] [DecidableEq S] [DecidableEq Pre]
    (cls : Wit → S) (states : Finset S) (hcls : ∀ w, cls w ∈ states)
    (pref : Wit → Pre) (b D : ℕ)
    (hfib : ∀ p, (Finset.univ.filter fun w => pref w = p).card ≤ b)
    (hD : ∀ s ∈ states, ((Finset.univ.filter fun w => cls w = s).image pref).card ≤ D) :
    Fintype.card Wit ≤ states.card * (b * D) := by
  have hsum : Fintype.card Wit = ∑ s ∈ states, (Finset.univ.filter fun w => cls w = s).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun w _ => hcls w
  rw [hsum]
  refine (Finset.sum_le_sum (g := fun _ => b * D) fun s hs => ?_).trans (by simp)
  refine (Finset.card_le_mul_card_image _ b fun p _ => ?_).trans
    (Nat.mul_le_mul_left b (hD s hs))
  exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans
    (by simpa [Finset.filter_filter] using
      (Finset.card_le_card (Finset.filter_subset (fun w => pref w = p) _)).trans (hfib p))
