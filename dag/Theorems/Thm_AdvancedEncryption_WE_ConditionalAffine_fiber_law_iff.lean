import Mathlib

theorem AdvancedEncryption.WE.ConditionalAffine.fiber_law_iff {V W : Type} [AddCommGroup V] [AddCommGroup W] [Finite V]
    (f : V →+ W) (d : W) :
    (∀ y : W, Nat.card {r : V // f r = y} = Nat.card {r : V // f r + d = y}) ↔
    ∃ s : V, f s = d := by
  sorry
