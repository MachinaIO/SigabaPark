import Definitions.Def_WE_WirePolarity

open AdvancedEncryption.WE.CircuitSAT AdvancedEncryption.WE.CircuitSAT.WirePolarity

theorem AdvancedEncryption.WE.CircuitSAT.polarity_encBit_exact {n s : ℕ} (φ : Circuit n s) :
    let p := analyze n φ.gates
    (∀ x : Fin n → Bool, Satisfies φ x →
      Satisfies φ (liftBits p (fun i ↦ x i.val))) ∧
    (∀ β : Bool, encBit (n := n) φ.gates β = true ↔ β = true ∧ ∃ x, Satisfies φ x) := by
  sorry
