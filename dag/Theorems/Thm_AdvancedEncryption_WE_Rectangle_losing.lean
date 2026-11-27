import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem AdvancedEncryption.WE.Rectangle.losing {I : Type} (A J C : Set I) :
    ¬ Wins A J C ↔ ∀ j ∈ J, (∀ i ∈ A, i = j) ∨ (∀ k ∈ C, k = j) := by sorry
