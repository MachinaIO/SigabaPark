import Mathlib

theorem AdvancedEncryption.WE.LiftedProduct.signed_decoding (t p x : ℤ) (hl : -32768 ≤ x) (hu : x ≤ 32768) :
    ((2*t) % (2*p)) / 2 = t % p ∧
    (if x % 65537 ≤ 32768 then x % 65537 else x % 65537 - 65537) = x := by sorry
