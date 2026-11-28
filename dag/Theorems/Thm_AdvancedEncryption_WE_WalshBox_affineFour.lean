import Definitions.Def_NandWalshBox
open NandWalshBox
theorem AdvancedEncryption.WE.WalshBox.affineFour (σ : Equiv.Perm (Fin 4)) (x y : Fin 4) :
    σ (xor4 x y) = xor4 (xor4 (σ x) (σ y)) (σ 0) := by sorry
