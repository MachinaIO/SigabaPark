import Definitions.Def_SwitchClauseBank
import Mathlib.Tactic

theorem solution {I : Type*} (F : Set (Set I)) (i j : I) :
    (j ∈ SwitchClauseBank.forced F i ∧
      ¬ ∃ k ∈ SwitchClauseBank.forced F i,
        SwitchClauseBank.forced F k ≠ SwitchClauseBank.forced F i ∧
        j ∈ SwitchClauseBank.forced F k) ↔
      SwitchClauseBank.forced F j = SwitchClauseBank.forced F i := by
  have refl (a : I) : a ∈ SwitchClauseBank.forced F a := fun _ _ h ↦ h
  have sub {a b : I} (hab : b ∈ SwitchClauseBank.forced F a) :
      SwitchClauseBank.forced F b ⊆ SwitchClauseBank.forced F a :=
    fun _ h t ht ha ↦ h t ht (hab t ht ha)
  constructor
  · rintro ⟨h, hn⟩
    by_contra he
    exact hn ⟨j, h, he, refl j⟩
  · intro he
    refine ⟨he ▸ refl j, ?_⟩
    rintro ⟨k, hk, hne, hj⟩
    exact hne (Set.Subset.antisymm (sub hk) (he ▸ sub hj))
