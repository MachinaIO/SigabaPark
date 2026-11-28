import Mathlib

theorem AdvancedEncryption.WE.FactoredRow.SlotNand {R : Type*} [CommRing R] (G r Bx By s x y ex ey : R) (h : G*r = -Bx) :
    -r*((By+y*G)*s+ey) - y*((Bx+x*G)*s+ex) =
    ((-By*r-G)+(1-x*y)*G)*s + (-r*ey-y*ex) := by sorry
