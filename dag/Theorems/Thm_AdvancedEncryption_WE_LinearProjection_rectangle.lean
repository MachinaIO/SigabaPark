import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem AdvancedEncryption.WE.LinearProjection.rectangle {I W : Type*} [Fintype I] [Fintype W] (A B : W→I→Prop)
    (diag : ∀ i, ∃ w,A w i ∧ B w i)
    (exactSupport : ∀ w i j,A w i→B w j→i=j) :
    Fintype.card I ≤ Fintype.card W := by sorry
