import Mathlib

theorem AdvancedEncryption.WE.FactoredRow.MixedLane {R : Type*} [CommRing R] (B G s00 s01 s10 s11 : R) :
    (B+G)*s11 - (B+G)*s10 - B*s01 + B*s00 =
      B*(s11-s10-s01+s00) + G*(s11-s10) := by sorry
