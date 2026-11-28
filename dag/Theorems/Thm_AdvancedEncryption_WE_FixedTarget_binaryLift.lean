import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem AdvancedEncryption.WE.FixedTarget.binaryLift (x y : Bool) (k : ℤ) :
    ((x.toNat : ℤ) - y.toNat)^2 ≤ ((x.toNat : ℤ) - y.toNat + 2*k)^2 := by sorry
