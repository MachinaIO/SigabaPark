import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem AdvancedEncryption.WE.Rectangle.incoming {m w : ℕ} (seed : Fin w → Bool) (rows : Fin m → Fin w → Bool) :
    ∃! pads : Fin m → Fin w → Bool, ∀ i t, (seed t ^^ pads i t) = rows i t := by sorry
