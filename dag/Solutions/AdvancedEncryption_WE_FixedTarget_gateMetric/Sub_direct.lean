import Definitions.Def_FixedTargetGeometry
open FixedTarget225
theorem solution : ∀ a b z : Bool,
    gateDist a b z = (if z == !(a && b) then 1 else 3) := by decide
