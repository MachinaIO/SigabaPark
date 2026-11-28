import Definitions.Def_NandWalshBox
open NandWalshBox
theorem AdvancedEncryption.WE.WalshBox.selectorLift (a b c : Bool) (t : Bool × Bool × Bool × Bool × Bool) :
    liftOK a b c t ↔ c = !(a && b) ∧ t = ((!a && !b),(!a && b),(a && !b),(a && b),a) := by sorry
