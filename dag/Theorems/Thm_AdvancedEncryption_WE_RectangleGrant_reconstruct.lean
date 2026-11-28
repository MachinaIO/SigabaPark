import Definitions.Def_RectangleGrant
open RectangleGrant
theorem AdvancedEncryption.WE.RectangleGrant.reconstruct (p q r b : Bool) :
    Bool.xor (Bool.xor p (masked false p r b)) (Bool.xor q (masked true q r b)) = b := by sorry
