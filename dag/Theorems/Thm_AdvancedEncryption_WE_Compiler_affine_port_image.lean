import Mathlib

theorem AdvancedEncryption.WE.Compiler.affine_port_image {K X E P : Type*} [Field K] [AddCommGroup X] [Module K X]
    [AddCommGroup E] [Module K E] [AddCommGroup P] [Module K P]
    (equations : X →ₗ[K] E) (ports : X →ₗ[K] P) (rhs : E) (guard : P → Prop)
    {ι : Type*} (check : ι → Module.Dual K (E × P))
    (complete : Submodule.span K (Set.range check) =
      (LinearMap.range (equations.prod ports)).dualAnnihilator) (y : P) :
    (∃ x, equations x = rhs ∧ ports x = y ∧ guard (ports x)) ↔
      guard y ∧ ∀ i, check i (rhs, y) = 0 := by sorry
