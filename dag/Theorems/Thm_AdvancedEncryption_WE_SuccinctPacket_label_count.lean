import Mathlib

theorem AdvancedEncryption.WE.SuccinctPacket.label_count (d m κ : ℕ) (enough : d + κ ≤ m) (prediction : (Fin d → Bool) → (Fin m → Bool)) :
    ((Finset.univ.image prediction).card : ℕ) * 2 ^ κ ≤ 2 ^ m := by sorry
