import Mathlib

theorem AdvancedEncryption.WE.PrivateMIFE.full_table_admissibility {W T : Type*} (decode : T → W)
    (covers : Function.Surjective decode) (accepts : W → Bool) :
    (∀ row, (false && accepts (decode row)) = (true && accepts (decode row))) ↔
      ∀ w, accepts w = false := by sorry
