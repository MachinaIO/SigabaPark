import Mathlib

theorem AdvancedEncryption.WE.OfflineCDS.OccurrencePooling (test : Fin 3 → Bool → Bool → Prop)
    (h0 : ∀ u v, test 0 u v ↔ u = false)
    (h1 : ∀ u v, test 1 u v ↔ v = true)
    (h2 : ∀ u v, test 2 u v ↔ u = v) :
    (∀ i, ∃ u v, test i u v) ∧ ¬ ∃ u v, ∀ i, test i u v := by sorry
