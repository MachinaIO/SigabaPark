import Mathlib

theorem AdvancedEncryption.WE.OfflineCDS.CoreCompletionAccept {C Y I : Type*} (test : I → C → Y → Prop) (i : Finset I) (core : C) (opening : Y)
    (accepted : ∀ a ∈ i, test a core opening) : ∃ extension, ∀ a ∈ i, test a core extension := by sorry
