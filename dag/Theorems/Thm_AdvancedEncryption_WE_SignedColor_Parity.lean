import Definitions.Def_SignedColorEnergy

open SignedColorEnergy

theorem AdvancedEncryption.WE.SignedColor.Parity {n m : ℕ} (l r : Fin m → Fin n) :
    (∀ v t, parityFeasible l r v t →
      objective l r (fun i ↦ (v i).round) ≤ energy v t) ∧
    (∀ c : Fin n → Color, ∃ v t, parityFeasible l r v t ∧ energy v t = objective l r c) := by sorry
