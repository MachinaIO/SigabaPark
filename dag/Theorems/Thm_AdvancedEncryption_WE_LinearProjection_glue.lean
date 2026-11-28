import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem AdvancedEncryption.WE.LinearProjection.glue {K E A B : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (L : E→ₗ[K]A) (R : E→ₗ[K]B) (V : Submodule K E) (x y : E) :
    x-y∈fibre L R V ↔ ∃ z, L z=L x ∧ R z=R y ∧ x-z∈V ∧ z-y∈V := by sorry
