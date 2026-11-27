import Mathlib

theorem AdvancedEncryption.WE.CBDWirePad.tree_capacity (K G I R T : ℕ) (hk : 0 < K)
    (hroot : R ≤ 2*(I+G)) (hleaf : 8*G*K ≤ (R+T)*K) : 6*G ≤ T+2*I := by sorry
