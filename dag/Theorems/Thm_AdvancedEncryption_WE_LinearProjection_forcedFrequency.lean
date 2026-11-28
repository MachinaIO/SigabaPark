import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem AdvancedEncryption.WE.LinearProjection.forcedFrequency {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (F G : Set E) (U W : Submodule K E) (le : U≤W)
    (good : ∀ a∈F, ∀ b∈G, a-b∈W → a∈W) {a b : E}
    (af : a∈F) (bg : b∈G) (h : a-b∈U) :
    U ⊔ Submodule.span K {a} ≤ W := by sorry
