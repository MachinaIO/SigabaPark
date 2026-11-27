import Definitions.Def_TerminalRectangle

open TerminalRectangle

theorem AdvancedEncryption.WE.Rectangle.terminal (h : HiddenRole) (t j : Bool) (a c : Bool → Bool) (u v : Bool) :
    (body t j (a true) (c true) =
      (body t j (a false) (c false) ^^ body t j (a false) (c true) ^^ body t j (a true) (c false))) ∧
    body (!t) (flipJoin h j)
      (flipLeft h (a u))
      (flipRight h (c v)) = body t j (a u) (c v) := by sorry
