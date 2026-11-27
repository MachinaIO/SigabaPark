import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.EdgeSpace.disjoint {ι V : Type} [Fintype ι] [AddCommGroup V]
    {W : ι → Type} [∀ i, AddCommGroup (W i)]
    (r : (i : ι) → V →+ W i) (s : V)
    (no : ¬ ∃ g : ι → V, ∑ i, g i = s ∧ ∀ i, r i (g i) = 0)
    (a b : ι → V) (ha : ∑ i, a i = 0) (hb : ∑ i, b i = s) :
    ¬ (∀ i, r i (a i) = r i (b i)) := by sorry
