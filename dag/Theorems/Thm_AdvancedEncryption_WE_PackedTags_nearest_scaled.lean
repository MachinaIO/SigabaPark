import Mathlib
/-- Nearest scaled decoding is invariant under full ciphertext wraps. -/
theorem AdvancedEncryption.WE.PackedTags.nearest_scaled (p step x e wrap : ℤ) (hs : 0 < step)
    (lo : 0 ≤ e + step/2) (hi : e + step/2 < step) :
    ((step*x + e + (p*step)*wrap + step/2)/step) % p = x % p := by sorry
