import Mathlib

theorem AdvancedEncryption.WE.PublicTail.cofactor_gate {P U : Type} (phi : P → U → Prop) (payload : Prop) (p : P) (u : U) :
    (phi p u ∧ (payload ∧ ∃ v, phi p v)) ↔ (payload ∧ phi p u) := by sorry
