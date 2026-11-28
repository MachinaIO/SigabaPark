import Mathlib

theorem solution {V : Type} [DecidableEq V] (S : Finset V) (H : Finset V → Prop) [DecidablePred H]
    (top : H S) (par : Even ((S.powerset.filter H).card)) :
    ∃ T, T ⊂ S ∧ H T := by
  classical
  by_contra h
  have hs : S.powerset.filter H = {S} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨sub,ht⟩
      by_contra ne
      exact h ⟨T, lt_of_le_of_ne sub ne, ht⟩
    · rintro rfl
      exact ⟨Finset.Subset.rfl, top⟩
  rw [hs, Finset.card_singleton] at par
  exact (by decide : ¬ Even 1) par
