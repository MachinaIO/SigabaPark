import Definitions.Def_NandWalshBox
open NandWalshBox
theorem AdvancedEncryption.WE.WalshBox.classification :
    ({M : Matrix (Fin 4) (Fin 4) ℚ | admissible M} : Set _) =
      (doublyStochastic ℚ (Fin 4) : Set _) ∧
    Set.extremePoints ℚ {M : Matrix (Fin 4) (Fin 4) ℚ | admissible M} =
      {σ.permMatrix ℚ | σ : Equiv.Perm (Fin 4)} ∧
    (∀ u v : Fin 4, forbidden (raw u v) = true ↔
      (u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0)) := by sorry
