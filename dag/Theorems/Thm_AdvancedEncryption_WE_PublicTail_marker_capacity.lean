import Mathlib

theorem AdvancedEncryption.WE.PublicTail.marker_capacity (b h k : ℕ) (decode : Fin (2^k) → Fin (2^b) → Fin (2^h))
    (onto : Function.Surjective decode) : h*2^b ≤ k := by sorry
