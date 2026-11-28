import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem AdvancedEncryption.WE.FixedTarget.scaledFrame {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (F G : X →ₗ[K] Y) (t : X) (a : K)
    (ha : a ≠ 0) (h : F (a • t) = G (a • t)) : F t = G t := by sorry
