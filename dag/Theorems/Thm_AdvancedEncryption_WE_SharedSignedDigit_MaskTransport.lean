import Mathlib

theorem AdvancedEncryption.WE.SharedSignedDigit.MaskTransport {V R : Type*} [AddCommGroup V] [AddCommGroup R]
    (L : V →+ R) (s d : V) (m : R) :
    (L s + m) - L (s + d) = m - L d := by sorry
