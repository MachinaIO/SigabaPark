import Definitions.Def_VariableTagFront

theorem AdvancedEncryption.WE.VariableTag.TagWitness (f : Fin 16 → Fin 256 → Fin 16) (v : Fin 16) :
    (∀ i, ∃ u, f i u = v) ↔ ∃ w : Fin 16 → Fin 256, ∀ i, f i (w i) = v := by sorry
