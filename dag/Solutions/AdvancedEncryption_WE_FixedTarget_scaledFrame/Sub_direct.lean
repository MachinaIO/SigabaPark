import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (F G : X →ₗ[K] Y) (t : X) (a : K)
    (ha : a ≠ 0) (h : F (a • t) = G (a • t)) : F t = G t := by
  rw [map_smul,map_smul] at h
  simpa [smul_smul,ha] using congrArg (fun z : Y => a⁻¹ • z) h
