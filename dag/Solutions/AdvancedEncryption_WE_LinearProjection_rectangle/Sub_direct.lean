import Definitions.Def_LinearObservationJoin
open ObservationJoin
theorem solution {I W : Type*} [Fintype I] [Fintype W] (A B : W→I→Prop)
    (diag : ∀ i, ∃ w,A w i ∧ B w i)
    (exactSupport : ∀ w i j,A w i→B w j→i=j) :
    Fintype.card I ≤ Fintype.card W := by
  classical
  choose f hf using diag
  apply Fintype.card_le_of_injective f
  intro i j h
  exact exactSupport (f i) i j (hf i).1 (h ▸ (hf j).2)
