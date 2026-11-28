import Mathlib

theorem AdvancedEncryption.WE.FactoredRow.ThreeMaster {R : Type*} [CommRing R] (B G c x y z : R) :
    let w := y+z-c*x
    c*(B*x) - (B+G)*y - B*z + (B+G)*w = G*(z-c*x) ∧
    c*(B*x) - B*y - (B+G)*z + (B+G)*w = G*(y-c*x) ∧
    (B+G)*y-c*(B*x)-(B+G)*(y-c*x) = c*G*x := by sorry
