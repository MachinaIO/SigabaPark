import Mathlib

theorem AdvancedEncryption.WE.Separator.functional_sink {V : Type*} (arc : V → V → Prop) (target : V)
    (uniqueNext : ∀ u v w, arc u v → arc u w → v = w)
    (sink : ∀ v, ¬ arc target v) (s : V) :
    Relation.EqvGen arc s target ↔ Relation.ReflTransGen arc s target := by sorry
