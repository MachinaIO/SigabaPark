import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Linarith

theorem solution {ι X : Type*}
    (S : Finset ι) (P : Finset (ι → X)) (hne : P.Nonempty)
    (hfresh : ∀ g ∈ P, ∀ w ∈ S, ∃ g' ∈ P, g' w ≠ g w ∧ ∀ v, v ≠ w → g' v = g v) :
    2 ^ S.card ≤ P.card := by
  classical
  induction S using Finset.induction_on generalizing P with
  | empty => simpa using Finset.card_pos.mpr hne
  | insert a S ha ih =>
    obtain ⟨g, hg⟩ := hne
    obtain ⟨g', hg', hne', -⟩ := hfresh g hg a (Finset.mem_insert_self a S)
    have key : ∀ x, (P.filter (fun f => f a = x)).Nonempty →
        2 ^ S.card ≤ (P.filter (fun f => f a = x)).card := by
      intro x hx
      apply ih _ hx
      intro f hf w hw
      rw [Finset.mem_filter] at hf
      obtain ⟨f', hf', h1, h2⟩ := hfresh f hf.1 w (Finset.mem_insert_of_mem hw)
      have hwa : w ≠ a := fun h => ha (h ▸ hw)
      refine ⟨f', Finset.mem_filter.mpr ⟨hf', ?_⟩, h1, h2⟩
      rw [h2 a (Ne.symm hwa)]; exact hf.2
    have h1 := key (g a) ⟨g, Finset.mem_filter.mpr ⟨hg, rfl⟩⟩
    have h2 := key (g' a) ⟨g', Finset.mem_filter.mpr ⟨hg', rfl⟩⟩
    have hdisj : Disjoint (P.filter (fun f => f a = g a)) (P.filter (fun f => f a = g' a)) := by
      rw [Finset.disjoint_filter]; intro f _ h h'; exact hne' (h'.symm.trans h)
    have hsub : (P.filter (fun f => f a = g a)) ∪ (P.filter (fun f => f a = g' a)) ⊆ P := by
      intro f hf; rcases Finset.mem_union.mp hf with h | h <;> exact (Finset.mem_filter.mp h).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at this
    rw [Finset.card_insert_of_notMem ha, pow_succ]
    omega
