import Mathlib

theorem AdvancedEncryption.WE.JoinRoute.signed_three {R : Type} [CommRing R] [IsDomain R] (two : (2:R) ≠ 0) (i j k : R) :
    (i+k-j)^2 - (i^2+k^2-j^2) = 0 ↔ i = j ∨ k = j := by
  sorry
