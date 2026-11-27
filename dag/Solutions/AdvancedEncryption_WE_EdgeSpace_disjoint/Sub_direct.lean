import Mathlib

open scoped BigOperators

theorem solution {ι V : Type} [Fintype ι] [AddCommGroup V]
    {W : ι → Type} [∀ i, AddCommGroup (W i)]
    (r : (i : ι) → V →+ W i) (s : V)
    (no : ¬ ∃ g : ι → V, ∑ i, g i = s ∧ ∀ i, r i (g i) = 0)
    (a b : ι → V) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = s) :
    ¬ (∀ i, r i (a i) = r i (b i)) := by
  intro same
  apply no
  refine ⟨fun i => b i - a i, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib, ha, hb, sub_zero]
  · intro i
    rw [map_sub, same, sub_self]
