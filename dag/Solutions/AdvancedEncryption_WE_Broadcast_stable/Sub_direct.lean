import Definitions.Def_SemSep

open SemSep

theorem solution : (∀ s∈evenStates,∀ x,step s x false∈oddStates) ∧
    (∀ s∈oddStates,∀ x,step s x false∈evenStates) ∧
    (∀ s∈shapes 4,s∈evenStates) ∧
    (shapes 0).length=1 ∧ (shapes 1).length=2 ∧ (shapes 2).length=4 ∧ (shapes 3).length=5 := by
  have h4 : ∀ s∈shapes 4,s∈evenStates := by
    have h : (shapes 4).all (fun t => evenStates.contains t) = true := by decide
    simpa using List.all_eq_true.mp h
  refine ⟨?_,?_,?_,by decide,by decide,by decide,by decide⟩
  · intro s hs x; simp [evenStates] at hs
    rcases hs with h|h|h|h|h <;> subst s <;> cases x <;> decide
  · intro s hs x; simp [oddStates] at hs
    rcases hs with h|h|h|h|h <;> subst s <;> cases x <;> decide
  · exact h4
