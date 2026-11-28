import Definitions.Def_SemSep

open SemSep

theorem AdvancedEncryption.WE.Broadcast.stable : (∀ s∈evenStates,∀ x,step s x false∈oddStates) ∧
    (∀ s∈oddStates,∀ x,step s x false∈evenStates) ∧
    (∀ s∈shapes 4,s∈evenStates) ∧
    (shapes 0).length=1 ∧ (shapes 1).length=2 ∧ (shapes 2).length=4 ∧ (shapes 3).length=5 := by sorry
