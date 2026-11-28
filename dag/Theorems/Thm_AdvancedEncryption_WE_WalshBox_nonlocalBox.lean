import Definitions.Def_NandWalshBox
open NandWalshBox
theorem AdvancedEncryption.WE.WalshBox.nonlocalBox :
    (∀ h k x r : Bool, flip h k x (flip h k x r) = r) ∧
    ¬ ∃ f g : Bool → Bool, ∀ x y, (f x ^^ g y) = (x && y) := by sorry
