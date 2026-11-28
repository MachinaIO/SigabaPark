import Mathlib

theorem AdvancedEncryption.WE.SharedSignedDigit.RadixRead (rest h : ℕ) (b : Bool) (hh : 0 < h) (hle : h < 4) :
    ((4 * rest + (if b then h else 0)) % 4 ≠ 0) ↔ b = true := by sorry
