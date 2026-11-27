import Mathlib

open scoped BigOperators

theorem AdvancedEncryption.WE.EdgeSpace.exact {ι V : Type} [Fintype ι] [AddCommGroup V]
    {W : ι → Type} [∀ i, AddCommGroup (W i)]
    (r : (i : ι) → V →+ W i) (s : V) :
    (∃ g : ι → V, ∑ i, g i = s ∧ ∀ i, r i (g i) = 0) ↔
    ∀ y : (i : ι) → W i, Nonempty
      (({a : ι → V // ∑ i, a i = 0 ∧ ∀ i, r i (a i) = y i}) ≃
       ({a : ι → V // ∑ i, a i = s ∧ ∀ i, r i (a i) = y i})) := by sorry
