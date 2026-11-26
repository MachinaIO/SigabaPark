import Mathlib

theorem solution {V : Type*} (arc : V → V → Prop) (target : V)
    (uniqueNext : ∀ u v w, arc u v → arc u w → v = w)
    (sink : ∀ v, ¬ arc target v) (s : V) :
    Relation.EqvGen arc s target ↔ Relation.ReflTransGen arc s target := by
  let R := Relation.ReflTransGen arc
  have step : ∀ u v, arc u v → (R u target ↔ R v target) := by
    intro u v huv
    constructor
    · intro h
      rcases Relation.ReflTransGen.cases_head h with h | ⟨w, huw, rest⟩
      · subst u
        exact False.elim (sink v huv)
      · exact uniqueNext u w v huw huv ▸ rest
    · exact fun h => Relation.ReflTransGen.head huv h
  constructor
  · intro h
    have same : ∀ x y, Relation.EqvGen arc x y → (R x target ↔ R y target) := by
      intro x y path
      induction path with
      | rel x y e => exact step x y e
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih hj => exact ih.trans hj
    exact (same _ _ h).mpr .refl
  · intro h
    clear step sink R
    induction h with
    | refl => exact .refl _
    | tail _ e ih => exact .trans _ _ _ ih (.rel _ _ e)
